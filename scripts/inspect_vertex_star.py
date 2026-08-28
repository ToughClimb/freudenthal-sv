#!/usr/bin/env python3
"""Inspect and integrity-check the exact vertex-star certificate."""
from __future__ import annotations

import argparse
import json
from collections import Counter, defaultdict
from hashlib import sha256
from math import isqrt
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
DEFAULT_CERTIFICATE = ROOT / "certificates" / "vertex_star_certificate.json"
GENERATOR = ROOT / "certificates" / "vertex_star_certificate.py"
SCHEMA_VERSION = "freudenthal-vertex-star-v1"
EXPECTED_TYPE_COUNTS = {
    1: {"corner_six_tet": 2, "corner_two_tet": 6},
    2: {
        "boundary_edge_eight_tet": 6,
        "boundary_edge_four_tet": 6,
        "boundary_face_twelve_tet": 6,
        "corner_six_tet": 2,
        "corner_two_tet": 6,
        "interior_twenty_four_tet": 1,
    },
    3: {
        "boundary_edge_eight_tet": 12,
        "boundary_edge_four_tet": 12,
        "boundary_face_twelve_tet": 24,
        "corner_six_tet": 2,
        "corner_two_tet": 6,
        "interior_twenty_four_tet": 8,
    },
}
EXPECTED_DIMENSION = {
    "corner_two_tet": 0,
    "boundary_edge_four_tet": 0,
    "corner_six_tet": 3,
    "boundary_edge_eight_tet": 5,
    "boundary_face_twelve_tet": 8,
    "interior_twenty_four_tet": 18,
}


def is_prime(number):
    if number < 2:
        return False
    if number % 2 == 0:
        return number == 2
    return all(number % divisor for divisor in range(3, isqrt(number) + 1, 2))


def relation_hash(relations):
    digest = sha256(f"relations={len(relations)}\n".encode())
    for row_number, row in enumerate(relations):
        digest.update(f"row={row_number}\n".encode())
        for column, numerator, denominator in row:
            digest.update(f"{column} {numerator}/{denominator}\n".encode())
    return digest.hexdigest()


def expected_record_id(record):
    coordinates = ",".join(str(value) for value in record["target_vertex"])
    return f"N{record['grid_shape'][0]}:a({coordinates})"


def hexadecimal(value):
    return (
        len(value) == 64
        and all(character in "0123456789abcdef" for character in value)
    )


def check_minor(witness, exact_rank, modulus, row_count, column_count, record_id):
    if witness["prime"] != modulus:
        raise AssertionError((record_id, "minor modulus"))
    if witness["rank"] != exact_rank:
        raise AssertionError((record_id, witness["rank"], exact_rank))
    if not 0 < witness["determinant_mod_prime"] < modulus:
        raise AssertionError((record_id, "zero modular determinant"))
    for key, bound in (("row_indices", row_count), ("column_indices", column_count)):
        indices = witness[key]
        if len(indices) != exact_rank or len(set(indices)) != exact_rank:
            raise AssertionError((record_id, key))
        if any(not isinstance(index, int) or not 0 <= index < bound for index in indices):
            raise AssertionError((record_id, key, "out of range"))


def check_rational(value, context):
    if not (
        isinstance(value, list)
        and len(value) == 2
        and all(isinstance(entry, int) for entry in value)
        and value[1] > 0
    ):
        raise AssertionError((context, "invalid rational encoding", value))


def validate(payload):
    if payload.get("schema_version") != SCHEMA_VERSION:
        raise AssertionError(payload.get("schema_version"))
    provenance = payload["provenance"]
    if provenance["generator_sha256"] != sha256(GENERATOR.read_bytes()).hexdigest():
        raise AssertionError("generator SHA-256 does not match local source")
    modulus = payload["arithmetic"]["modulus"]
    if not is_prime(modulus):
        raise AssertionError(("nonprime modulus", modulus))
    records = payload["records"]
    if len(records) != 99:
        raise AssertionError(("record count", len(records)))
    ids = [record["record_id"] for record in records]
    if len(ids) != len(set(ids)):
        raise AssertionError("duplicate record IDs")
    configurations = payload["classification"]["configurations"]
    classification = payload["classification"]
    if classification["record_count"] != len(records):
        raise AssertionError(("classified record count", classification["record_count"]))
    if len(configurations) != 6:
        raise AssertionError(("configuration count", len(configurations)))
    if classification["configuration_union_count"] != len(configurations):
        raise AssertionError("configuration union count")
    configuration_ids = {item["configuration_id"] for item in configurations}
    operators = payload["canonical_operators"]
    if set(operators) != configuration_ids:
        raise AssertionError("canonical-operator/configuration mismatch")
    if classification["canonical_operator_count"] != len(operators):
        raise AssertionError("canonical operator count")

    per_grid = defaultdict(Counter)
    per_configuration = Counter()
    for record in records:
        record_id = record["record_id"]
        if record["schema_version"] != SCHEMA_VERSION:
            raise AssertionError(record_id)
        if record_id != expected_record_id(record):
            raise AssertionError(record_id)
        if record["configuration_id"] not in configuration_ids:
            raise AssertionError((record_id, "unknown configuration"))
        grid = record["grid_shape"][0]
        if record["grid_shape"] != [grid, grid, grid] or grid not in EXPECTED_TYPE_COUNTS:
            raise AssertionError((record_id, "grid shape"))
        if record["target_rows"] != record["star_tetrahedra"]:
            raise AssertionError((record_id, "target/star row mismatch"))
        if record["mean_constraint_rows"] != record["star_tetrahedra"]:
            raise AssertionError((record_id, "mean/star row mismatch"))
        if record["off_target_vertex_rows"] != 3 * record["star_tetrahedra"]:
            raise AssertionError((record_id, "off-target row count"))
        if record["constraint_rows"] != (
            record["mean_constraint_rows"] + record["off_target_vertex_rows"]
        ):
            raise AssertionError((record_id, "constraint row total"))
        if record["jet_columns"] != 3 * record["active_nonboundary_edges"]:
            raise AssertionError((record_id, "jet column count"))
        if record["active_nonboundary_edges"] > record["incident_edges"]:
            raise AssertionError((record_id, "active edge count"))
        if record["lift_degree"] != 3 or record["target_degrees"] != [4, 5]:
            raise AssertionError((record_id, "degree metadata"))
        expected = EXPECTED_DIMENSION[record["kind"]]
        if record["jet_rank"] != expected:
            raise AssertionError((record_id, "jet rank"))
        if record["augmented_rank"] - record["constraint_rank"] != expected:
            raise AssertionError((record_id, "supported image rank"))
        if record["supported_image_dimension"] != expected:
            raise AssertionError((record_id, "supported dimension"))
        if record["compatibility_dimension"] != expected:
            raise AssertionError((record_id, "compatibility dimension"))
        if record["compatibility_codimension"] \
                != record["target_rows"] - expected:
            raise AssertionError((record_id, "compatibility codimension"))
        if not record["target_annihilators_equal"]:
            raise AssertionError((record_id, "annihilator equality"))
        if relation_hash(record["compatibility_relations_rref"]) \
                != record["compatibility_relations_sha256"]:
            raise AssertionError((record_id, "relation hash"))
        for field in (
            "star_geometry_sha256", "jet_matrix_sha256",
            "compatibility_relations_sha256", "constraint_matrix_sha256",
            "augmented_matrix_sha256",
        ):
            if not hexadecimal(record[field]):
                raise AssertionError((record_id, field))
        if len(record["compatibility_relations_rref"]) \
                != record["compatibility_codimension"]:
            raise AssertionError((record_id, "relation count"))
        for relation in record["compatibility_relations_rref"]:
            for column, numerator, denominator in relation:
                if not (
                    isinstance(column, int)
                    and 0 <= column < record["target_rows"]
                    and isinstance(numerator, int)
                    and isinstance(denominator, int)
                    and denominator > 0
                ):
                    raise AssertionError((record_id, "relation encoding"))
        check_minor(
            record["jet_matrix_minor"], record["jet_rank"], modulus,
            record["target_rows"], record["jet_columns"], record_id,
        )
        check_minor(
            record["constraint_matrix_minor"], record["constraint_rank"],
            modulus, record["constraint_rows"], record["velocity_columns"],
            record_id,
        )
        check_minor(
            record["augmented_matrix_minor"], record["augmented_rank"],
            modulus, record["constraint_rows"] + record["target_rows"],
            record["velocity_columns"], record_id,
        )
        per_grid[grid][record["kind"]] += 1
        per_configuration[(grid, record["configuration_id"])] += 1

    for grid, expected in EXPECTED_TYPE_COUNTS.items():
        if dict(sorted(per_grid[grid].items())) != expected:
            raise AssertionError((grid, dict(per_grid[grid]), expected))
        if classification["vertex_placement_count_by_grid"][str(grid)] \
                != sum(per_grid[grid].values()):
            raise AssertionError((grid, "placement metadata"))
        if classification["vertex_placement_count_by_grid_and_kind"][str(grid)] \
                != expected:
            raise AssertionError((grid, "type-count metadata"))
    for item in configurations:
        configuration_id = item["configuration_id"]
        for grid in (1, 2, 3):
            if item["placement_count_by_grid"][str(grid)] \
                    != per_configuration[(grid, configuration_id)]:
                raise AssertionError((configuration_id, grid))
        operator = operators[configuration_id]
        if operator["configuration_id"] != configuration_id:
            raise AssertionError((configuration_id, "operator ID"))
        if operator["kind"] != item["kind"]:
            raise AssertionError((configuration_id, "operator kind"))
        dimension = EXPECTED_DIMENSION[item["kind"]]
        verification = operator["verification"]
        if verification["basis_dimension"] != dimension:
            raise AssertionError((configuration_id, "operator dimension"))
        if len(operator["lift_basis"]) != dimension:
            raise AssertionError((configuration_id, "lift basis length"))
        if len(operator["selected_jet_columns"]) != dimension:
            raise AssertionError((configuration_id, "jet selection length"))
        if len(operator["selected_target_rows"]) != dimension:
            raise AssertionError((configuration_id, "target selection length"))
        if len(operator["coordinate_inverse"]) != dimension \
                or any(len(row) != dimension for row in operator["coordinate_inverse"]):
            raise AssertionError((configuration_id, "coordinate inverse shape"))
        if len(operator["target_basis"]) != verification["target_equations"] \
                or any(len(row) != dimension for row in operator["target_basis"]):
            raise AssertionError((configuration_id, "target basis shape"))
        if len(operator["velocity_nodes"]) * 3 != verification["velocity_columns"]:
            raise AssertionError((configuration_id, "velocity-node count"))
        if len(operator["target_tetrahedra"]) != verification["target_equations"]:
            raise AssertionError((configuration_id, "target-tetrahedron count"))
        if len(operator["active_edges"]) * 3 < dimension:
            raise AssertionError((configuration_id, "active-edge metadata"))
        if len(set(operator["selected_jet_columns"])) != dimension \
                or any(not 0 <= index < 3 * len(operator["active_edges"])
                       for index in operator["selected_jet_columns"]):
            raise AssertionError((configuration_id, "selected jet columns"))
        if len(set(operator["selected_target_rows"])) != dimension \
                or any(not 0 <= index < verification["target_equations"]
                       for index in operator["selected_target_rows"]):
            raise AssertionError((configuration_id, "selected target rows"))
        for row in operator["target_basis"] + operator["coordinate_inverse"]:
            for value in row:
                check_rational(value, configuration_id)
        for basis_vector in operator["lift_basis"]:
            columns = [entry[0] for entry in basis_vector]
            if columns != sorted(set(columns)):
                raise AssertionError((configuration_id, "lift-basis columns"))
            for column, numerator, denominator in basis_vector:
                if not (
                    isinstance(column, int)
                    and 0 <= column < verification["velocity_columns"]
                    and isinstance(numerator, int)
                    and isinstance(denominator, int)
                    and denominator > 0
                ):
                    raise AssertionError((configuration_id, "lift-basis encoding"))
    return len(records)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--certificate", type=Path, default=DEFAULT_CERTIFICATE)
    parser.add_argument("--validate", action="store_true")
    parser.add_argument("--record", help="print one record by stable record ID")
    parser.add_argument("--kind", help="list records for one of the six vertex types")
    parser.add_argument("--operators", action="store_true", help="list explicit canonical operators")
    args = parser.parse_args()
    try:
        payload = json.loads(args.certificate.resolve().read_text())
    except FileNotFoundError as exc:
        raise SystemExit(
            f"missing {args.certificate}; generate the vertex certificate first"
        ) from exc
    if args.validate:
        count = validate(payload)
        print(f"vertex-star record integrity passed: {count} records")
        if not any((args.record, args.kind, args.operators)):
            return
    if args.record:
        matches = [
            record for record in payload["records"]
            if record["record_id"] == args.record
        ]
        if len(matches) != 1:
            raise SystemExit(
                f"record ID matched {len(matches)} records: {args.record}"
            )
        print(json.dumps(matches[0], indent=2))
        return
    if args.kind:
        ids = [
            record["record_id"] for record in payload["records"]
            if record["kind"] == args.kind
        ]
        if not ids:
            raise SystemExit(f"no records for kind {args.kind!r}")
        print("\n".join(ids))
        return
    if args.operators:
        for configuration_id, operator in payload["canonical_operators"].items():
            print(
                configuration_id,
                operator["kind"],
                operator["representative_record_id"],
                operator["verification"]["basis_dimension"],
            )
        return
    compact = {
        "schema_version": payload["schema_version"],
        "generator_sha256": payload["provenance"]["generator_sha256"],
        "classification": payload["classification"],
    }
    print(json.dumps(compact, indent=2))


if __name__ == "__main__":
    main()
