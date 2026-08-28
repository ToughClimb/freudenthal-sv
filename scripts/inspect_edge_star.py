#!/usr/bin/env python3
"""Inspect and integrity-check the generated edge-star certificate records."""

from __future__ import annotations

import argparse
import json
from collections import Counter, defaultdict
from hashlib import sha256
from math import isqrt
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
DEFAULT_CERTIFICATE = ROOT / "certificates" / "edge_star_certificate.json"
DEFAULT_SUMMARY = ROOT / "certificates" / "edge_star_certificate.summary.json"
GENERATOR = ROOT / "certificates" / "edge_star_certificate.py"
SCHEMA_VERSION = "freudenthal-edge-star-v2"


def load(path: Path):
    try:
        return json.loads(path.read_text())
    except FileNotFoundError as exc:
        raise SystemExit(f"missing {path}; generate the certificate first") from exc


def relation_hash(rows):
    digest = sha256()
    for i, row in enumerate(rows):
        for j, numerator, denominator in row:
            digest.update(f"{i} {j} {numerator}/{denominator}\n".encode())
    return digest.hexdigest()


def is_prime(number):
    if number < 2:
        return False
    if number % 2 == 0:
        return number == 2
    return all(number % divisor for divisor in range(3,isqrt(number)+1,2))


def expected_record_id(record):
    endpoint=lambda values: ",".join(str(value) for value in values)
    return (
        f"N{record['grid_shape'][0]}:e({endpoint(record['edge'][0])})-"
        f"({endpoint(record['edge'][1])}):k{record['k']}"
    )


def validate(certificate, summary):
    if certificate.get("schema_version") != SCHEMA_VERSION:
        raise AssertionError(certificate.get("schema_version"))
    for key in (
        "schema_version", "provenance", "mathematical_input", "arithmetic",
        "classification_definitions", "classification",
    ):
        if certificate[key] != summary[key]:
            raise AssertionError(f"summary/full mismatch in {key}")

    provenance = certificate["provenance"]
    if provenance["generator_sha256"] != sha256(GENERATOR.read_bytes()).hexdigest():
        raise AssertionError("generator SHA-256 does not match the local source")
    records = certificate["records"]
    expected = 42 if provenance["mode"] == "representatives" else 3996
    if len(records) != expected:
        raise AssertionError((len(records), expected))
    ids = [record["record_id"] for record in records]
    if len(ids) != len(set(ids)):
        raise AssertionError("record_id values are not unique")

    expected_index = [{
        key: record[key] for key in (
            "record_id", "grid_shape", "edge", "k", "kind",
            "source_configuration_id", "coverage_configuration_id",
        )
    } for record in records]
    if summary["record_index"] != expected_index:
        raise AssertionError("summary record_index does not match full records")

    configuration_items = summary["classification"]["configurations"]
    configuration_map = {
        item["coverage_configuration_id"]:item for item in configuration_items
    }
    if len(configuration_map) != len(configuration_items):
        raise AssertionError("duplicate coverage configuration in summary")
    modulus=certificate["arithmetic"]["modulus"]
    if not is_prime(modulus):
        raise AssertionError(f"nonprime modular witness modulus: {modulus}")
    hexadecimal_hash_fields = (
        "source_star_geometry_sha256", "source_vertex_matrix_sha256",
        "source_augmented_matrix_sha256", "supported_patch_geometry_sha256",
        "supported_off_matrix_sha256", "target_annihilator_sha256",
        "supported_augmented_matrix_sha256",
    )
    for record in records:
        if record["schema_version"] != SCHEMA_VERSION:
            raise AssertionError(record["record_id"])
        if record["record_id"] != expected_record_id(record):
            raise AssertionError(record["record_id"])
        if record["coverage_configuration_id"] not in configuration_map:
            raise AssertionError(record["coverage_configuration_id"])
        configuration=configuration_map[record["coverage_configuration_id"]]
        if record["source_configuration_id"] not in configuration["source_configuration_ids"]:
            raise AssertionError(record["record_id"])
        if record["kind"] != configuration["kind"]:
            raise AssertionError(record["record_id"])
        if record["source_rank_vertex_augmented"] - record["source_rank_vertex"] \
                != record["source_trace_dimension"]:
            raise AssertionError(record["record_id"])
        if record["supported_rank_augmented"] - record["supported_rank_off"] \
                != record["lift_dimension"]:
            raise AssertionError(record["record_id"])
        if record["source_trace_dimension"] != record["lift_dimension"]:
            raise AssertionError(record["record_id"])
        witness = record["supported_augmented_minor"]
        if witness["prime"] != modulus:
            raise AssertionError(record["record_id"])
        if witness["rank"] != record["supported_rank_augmented"]:
            raise AssertionError(record["record_id"])
        if witness["determinant_mod_prime"] == 0:
            raise AssertionError(record["record_id"])
        if len(witness["row_indices"]) != witness["rank"] \
                or len(set(witness["row_indices"])) != witness["rank"]:
            raise AssertionError(record["record_id"])
        if len(witness["column_indices"]) != witness["rank"] \
                or len(set(witness["column_indices"])) != witness["rank"]:
            raise AssertionError(record["record_id"])
        if len(record["target_annihilator_rref"]) \
                != record["target_annihilator_dimension"]:
            raise AssertionError(record["record_id"])
        if relation_hash(record["target_annihilator_rref"]) \
                != record["target_annihilator_sha256"]:
            raise AssertionError(record["record_id"])
        for field in hexadecimal_hash_fields:
            value = record[field]
            if len(value) != 64 or any(c not in "0123456789abcdef" for c in value):
                raise AssertionError((record["record_id"], field, value))

    if provenance["mode"] == "exhaustive":
        classification = certificate["classification"]
        if classification["incidence_type_count"] != 7:
            raise AssertionError("incidence type count")
        if classification["source_configuration_union_count"] != 85:
            raise AssertionError("source configuration count")
        if classification["coverage_configuration_union_count"] != 180:
            raise AssertionError("coverage configuration count")
        expected_grid_counts = {
            "3": 279, "4": 604, "5": 1115,
        }
        if classification["edge_placement_count_by_grid"] != expected_grid_counts:
            raise AssertionError("edge placement counts")
        for grid,count in expected_grid_counts.items():
            indexed=sum(
                item["placement_count_by_grid"][grid]
                for item in configuration_items
            )
            if indexed != count:
                raise AssertionError((grid,indexed,count))
        if Counter(record["k"] for record in records) != Counter({4: 1998, 5: 1998}):
            raise AssertionError("degree record counts")
        degrees_by_edge=defaultdict(set)
        for record in records:
            degrees_by_edge[(tuple(record["grid_shape"]),tuple(map(tuple,record["edge"])))].add(record["k"])
        if len(degrees_by_edge) != 1998 or any(
            degrees != {4,5} for degrees in degrees_by_edge.values()
        ):
            raise AssertionError("each edge placement must have exactly the k=4,5 pair")
    return len(records)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--certificate", type=Path, default=DEFAULT_CERTIFICATE)
    parser.add_argument("--summary", type=Path, default=DEFAULT_SUMMARY)
    parser.add_argument("--validate", action="store_true")
    parser.add_argument("--record", help="print one exact record by stable record_id")
    parser.add_argument("--configuration", help="print one coverage class and its records")
    parser.add_argument("--kind", help="list record ids for one of the seven incidence types")
    parser.add_argument("--list-configurations", action="store_true")
    args = parser.parse_args()

    certificate = load(args.certificate.resolve())
    summary = load(args.summary.resolve())
    if args.validate:
        count = validate(certificate, summary)
        print(f"edge-star record integrity passed: {count} records")
        if not any((
            args.record, args.configuration, args.kind,
            args.list_configurations,
        )):
            return

    records = certificate["records"]
    if args.record:
        matches = [record for record in records if record["record_id"] == args.record]
        if len(matches) != 1:
            raise SystemExit(f"record_id matched {len(matches)} records: {args.record}")
        print(json.dumps(matches[0], indent=2))
        return
    if args.configuration:
        matches = [
            item for item in summary["classification"]["configurations"]
            if item["coverage_configuration_id"] == args.configuration
        ]
        if len(matches) != 1:
            raise SystemExit(
                f"coverage configuration matched {len(matches)} classes: "
                f"{args.configuration}"
            )
        result = dict(matches[0])
        result["record_ids"] = [
            record["record_id"] for record in records
            if record["coverage_configuration_id"] == args.configuration
        ]
        print(json.dumps(result, indent=2))
        return
    if args.kind:
        ids = [record["record_id"] for record in records if record["kind"] == args.kind]
        if not ids:
            raise SystemExit(f"no records for kind {args.kind!r}")
        print("\n".join(ids))
        return
    if args.list_configurations:
        for item in summary["classification"]["configurations"]:
            print(
                item["coverage_configuration_id"], item["kind"],
                item["representative_grid"], item["representative_edge"],
            )
        return

    compact = {
        "schema_version": summary["schema_version"],
        "mode": summary["provenance"]["mode"],
        "generator_sha256": summary["provenance"]["generator_sha256"],
        "classification": {
            key: value for key, value in summary["classification"].items()
            if key != "configurations"
        },
    }
    print(json.dumps(compact, indent=2))


if __name__ == "__main__":
    main()
