# Freudenthal–Scott–Vogelius Lean formalization

This independent Lean project proves the complete analytic
Freudenthal–Scott–Vogelius uniform divergence right-inverse theorem for
`k=4,5` on every cube mesh size `N ≥ 1`. The manuscript is maintained
separately and is not needed to compile the proofs. The higher-degree extension is outside the
claimed formalization scope.

The final unconditional theorems are in
[MainTheorem.lean](FreudenthalSVLean/MainTheorem.lean):

```lean
MainTheorem.quartic_uniform_right_inverse : FreudenthalMesh.HasUniformRightInverse 4
MainTheorem.quintic_uniform_right_inverse : FreudenthalMesh.HasUniformRightInverse 5
```

For each degree they prove one `C > 0` before all `N ≥ 1`, and on each mesh
one fixed linear map `R : Q →ₗ[ℝ] V` before all pressure inputs, such that
`div (R q) = q` and the actual gradient energy is at most `C²` times the
actual pressure L2 energy. `V` consists of actual conforming piecewise
polynomials with zero physical boundary values, and `Q` is exactly its
spatial divergence image. Mesh coverage, genuine Lebesgue integrals,
physical weak gradients and the standard smooth-closure `H¹₀` criterion
are proved, not assumed.

`MainTheorem.quartic_uniform_h1_right_inverse` and its quintic counterpart
give the full genuine H1-energy bounds. [DiscreteInfSup.lean](FreudenthalSVLean/DiscreteInfSup.lean)
proves the reduced inf-sup statement in quantified-witness form: for every
nonzero pressure, an actual nonzero velocity has strictly positive
denominator and genuine pairing ratio at least one fixed positive beta,
uniformly over N.

The proof chain is: genuine continuous cube divergence inverse → uniform
mean-preserving Fortin lift → supported vertex and edge corrections →
two-cube mean routing → element bubbles → the full discrete inverse.
The separate fixed `N=1` argument covers the small mesh. The continuous
inverse itself is proved using the actual Bogovskii integral, uniform
gradient estimates, exact divergence and mean identities, actual L2
convergence, smooth density and a complete-space geometric series; a
Hilbert-space linear section fixes the required operator quantifiers.

No Zhang-specific vertex lemma or external rank certificate is a proof
dependency. Finite identities and geometry checks in Lean are checked by
the kernel. No CAS, SMT or Python oracle is trusted. The whole-project
transitive axiom audit permits only `propext`, `Classical.choice`, and
`Quot.sound`; see [TRUST.md](TRUST.md) and `bash scripts/verify.sh`.

The checked mathematical foundation includes:

- the quartic matrix's rational two-sided inverse, `det A = -6`, and real
  scalar transport; equal-pair and checkerboard incidence spanning;
- generic Bernstein differentiation derived from `MvPolynomial.pderiv`,
  and its agreement with actual real Fréchet differentiation;
- coordinate-chain barycentric geometry, analytic edge-jet gradient
  reconstruction and its linear cubic correction, protected skeleton
  traces, and endpoint/middle edge-bubble identities; common traces imply
  common edge jets, and zero boundary traces imply zero issuing jets;
- arbitrary-degree Bernstein volume integration, derived from Lebesgue
  interval integration, the fundamental theorem of calculus, and Fubini;
- all eleven displayed quartic fields' actual real divergence edge traces
  and genuine volume means, including the matrix `A/30` and zero sum of the
  twelve means; their global nodal-product realization, actual conformity,
  rectangular zero trace, and fixed uniformly stable physical macro lift;
- positive-scale derivative, mean, and gradient-energy identities;
- an injective embedding into the actual reference Lebesgue `L²` space,
  positive definiteness of the square integral, fixed-degree linear-map
  and derivative bounds, and a vertex inverse estimate whose constant is
  independent of all translation, permutation, and scale parameters; and
- arbitrary-`N` mesh and finite-element algebra definitions, together with
  a proof that the closed tetrahedra cover exactly the cube, including all
  boundary and coordinate-tie cases, and contain their closed edge segments;
- structural face containment of distinct-element intersections, true
  zero-volume shared faces, actual conforming global element-bubble lifts,
  a uniformly stable right inverse on the zero-element-mean pressure image
  for `N ≥ 2`, and a true-energy finite-dimensional right inverse for `N=1`.

The global nodal functions have also been identified with their actual
piecewise-affine polynomial data for arbitrary integer lattice nodes.
This proves conformity and support without assuming mesh-intersection
compatibility. Quadratic/cubic endpoint products are proved to belong to
the defined velocity space, including homogeneous boundary values, and the
cubic products protect every non-designated local vertex. Nodal products
with arbitrary fixed exponents also satisfy the degree, conformity,
support, and boundary conditions under the stated boundary-plane criterion.
Fixed linear mean routing on a connected finite graph has a proved right-inverse
property and explicit graph-size norm bound. Its geometric hypotheses are
discharged for actual vertex stars and fixed face-connected cube clusters.
Every actual edge has a fixed connected rectangular cluster of at most
twenty-seven cubes, including all boundary configurations. Cubic face
transfers have actual two-tetrahedron
support, conformity, physical boundary values, paired divergence means,
all vertex protections, and a uniform physical gradient-energy bound.

Every actual vertex incidence is also parameterized exactly by a coordinate
order and a marked chain position. Admissibility is proved equivalent to
the three lower/interior/upper boundary tags, uniformly for every positive
`N`. The six star valences, canonical incident/active edge counts, and
coordinate/central-inversion actions are checked. The active condition is
proved equivalent to the boundary criterion used by the global nodal
bubbles. Six explicit rooted trees certify genuine three-vertex-face
adjacency; proved geometric graph isomorphisms transport their connectivity
to the actual star of every mesh vertex. The actual fixed linear routing
operator lifts every zero-sum vector of star element means, is zero on
every non-star element, preserves every mesh vertex-divergence value, and
satisfies `energy ≤ C h^{-3} sum m_T^2`, with one constant before all mesh
and vertex parameters.

The complete vertex stage is proved on the actual arbitrary-`N` mesh.
The compatibility map is derived from spatial differentiation of the
cubic barycentric fields. Common geometric edges share one input jet;
all omitted boundary edges have zero jet. Its exact image equals the
actual velocity's divergence-vertex image, and every pressure-image trace
belongs to it. Integer barycentric-gradient identities checked over all
twenty-seven boundary words prove cancellation of the true raw element
means, through an explicit mesh/catalog equivalence. A fixed bounded
linear inverse family, raw nodal fields, and fixed mean routing produce
supported cubic corrections with zero means and energy bounded by
`C h^3 sum d_T^2`. Global assembly uses precisely four contributing fields
per tetrahedron, counts every incidence once, and gives a linear operator
matching all vertex-divergence values with zero element means and
`energy ≤ C(k) pressureEnergy`, uniformly over every `N ≥ 1`. The initial
stable mean lift and actual weak-gradient/`H¹₀` smooth-closure interface
are proved as described below.

The edge-stage foundation is also connected to the actual mesh. Weighted
global face products of degrees four and five have proved conformity,
physical boundary values, two-owner support, zero vertex derivatives,
and complete target/spill/other-edge trace formulas. Actual conformity
implies conormal gradient jumps even at edge points. Boundary-face zero
trace implies conormal gradients and gives equal-pair or zero-source
compatibility under explicit geometric transversality hypotheses; four
shared faces give the checkerboard relation by intersection of two
independent conormal spaces. The actual geometry hypotheses for each
source cases are discharged by explicit canonical shared-face and
boundary-plane witnesses on the actual mesh, including all changing
endpoint tags. Proved physical mesh symmetries transport these constructions
to every edge orientation and boundary location.

Every arbitrary-mesh edge incidence is exactly parameterized by its first
endpoint's boundary word and its integer endpoint displacement. Increasing
edges have precisely the seven nonzero binary directions. Complete
tetrahedron vertex sets, not only incidence counts, are covered by the
seven canonical geometries under coordinate permutations and central
inversion with endpoint exchange. All boundary words and directions are
checked in the kernel; the proved mesh/catalog equivalence supplies the
finite-to-arbitrary-`N` implication. Each geometric edge has at most six
incident tetrahedra.

Actual pressure polynomials have a fixed linear coefficient extractor
and a proved complete homogeneous edge expansion. Zero endpoint values
leave exactly the two cubic or three quartic modes. Explicit coefficient
recovery in any real vector space transfers pointwise membership in any
linear compatibility subspace to every coefficient vector. The actual
edge-star data have a genuine-volume bound
`h^3 sum coefficients^2 ≤ C(d) sum incident integrals`, with one constant
before all mesh and edge parameters.

The canonical face-pattern table is regenerated from relative face nodes
and barycentric gradients on all twenty-four lattice states and every
local edge, including the borrowed face's second owner. Explicit integer
identities `B J + V W = I` and `W B = 0` give fixed bounded linear inverses
on the exact zero, equal-pair, checkerboard, and unrestricted source spaces,
without assuming a rank equality.

These finite identities are connected to actual spatial polynomials and
actual pressure data. Canonical pressure compatibility follows from the
proved face-jump and boundary conormal formulas with explicit geometric
witnesses. Exact trace decomposition gives all compatible coefficient
vectors. Actual conforming primary/borrowed face patterns produce the
complete target-edge traces and zero divergence traces on every other
mesh edge. Global endpoint-hat multiplication gives the quintic endpoint
and middle modes from the quartic patterns. Fixed linear maps match the
whole actual pressure edge trace and preserve every vertex derivative.
Genuine two-owner energy scaling and the explicit inverse give one bound
`energy <= C h^3 sum input-coefficient squares` before all mesh, canonical
type, and endpoint parameters for both degrees.

Coordinate permutations and central inversion now act on actual cells,
tetrahedra, grid vertices, boundary tags and physical points. They preserve
Lebesgue measure, conformity, polynomial degree, the actual gradient and
pressure energies, and divergence means. Endpoint exchange and the full
edge-star pressure integral sum are transported by explicit actual
incidence equivalences. Every actual edge has a fixed quartic and quintic
linear lift chosen before its pressure input, with a uniform bound by the
pressure energy of its edge star. Its polynomial support lies in an
endpoint star.

Global edge assembly is proved. Each mesh edge is stored once in increasing
orientation; exact incidence counting gives six pressure contributions per
tetrahedron, and endpoint-star support gives at most fifty-six contributing
fields per tetrahedron. The assembled edge operator matches every full
edge trace simultaneously, protects all vertex derivatives and has a
uniform actual integral energy bound. Composing it with the mean-preserving
vertex stage gives fixed quartic and quintic skeleton lifts on the exact
pressure image. Their divergence agrees with the pressure on every actual
edge, and their energy is uniformly bounded by the full pressure energy.
The unadjusted skeleton residual remains in the divergence image and
vanishes on every edge.

The mean-preserving edge and skeleton stages are also proved for every
`N ≥ 2`. Actual barycentric monomial integration gives the paired means
of all one-power and bilinear weighted face fields. Their total divergence
mean is zero, including borrowed faces and all transported boundary cases.
Each local edge map is corrected by a fixed bounded cube-cluster router;
the correction preserves every full edge trace and removes every actual
element mean. The proved bound
`sum elementMeans² ≤ h³/2 * velocityEnergy` cancels the router's `h^{-3}`
factor. Its support is confined to the cluster and adjacent cubes. An
injective offset/direction encoding gives at most `5³ * 7 = 875` such
neighborhoods per tetrahedron, uniformly in `N`. Summation and exact
six-fold pressure incidence counting give fixed uniformly stable global
mean-preserving edge maps. Composition with the vertex stage gives
uniformly stable skeleton maps whose residuals have exactly the input
element means. The proved initial stable mean lift and final element
bubbles complete the unrestricted right-inverse theorem for both degrees.

The quartic two-cube macro stage is proved on the actual mesh. Each of the
thirty-three displayed terms is a normalized product of four fixed global
lattice-node hats. A kernel-checked integer/natural node certificate and
the generic monomial product formula identify its polynomial restriction
on all twelve reference tetrahedra. One global continuous function proves
conformity on every shared point; positive-exponent nodes away from all six
rectangular boundary planes prove the full zero exterior trace. The fixed
coefficient map `30 A^{-1}` recovers every compatible twelve-vector of actual
volume means and has a genuine gradient-integral energy bound. Proved
affine lattice transport and scaling give homogeneous conforming quartic
fields on every admissible two-cube patch, including physical-boundary
patches. An explicit all-origin/all-permutation coverage theorem identifies
precisely its twelve actual owners and proves that every nonowner carries
the zero polynomial. The physical lift is linear, has zero divergence on
every actual local edge, and satisfies
`velocityEnergy ≤ C h^{-3} sum m_T^2`, with one positive constant before all
mesh, translation, permutation, patch and input quantifiers. Two-cube
transfers now give a fixed linear mean router on any nonempty
face-connected finite cube cluster. Connectedness of the element graph
follows from cube connectedness and within-cube adjacency, and simple
rooted paths give a bound depending only on the cluster size. Coordinate
paths prove actual rectangular-cluster connectedness for arbitrary `N`;
the edge clusters have at most twenty-seven cubes and 162 tetrahedra.
No cluster, root, path, patch, or local map is chosen from the input field.

The element-bubble stage now includes a complete local algebraic proof.
Every degree-bounded spatial polynomial has a homogeneous barycentric
representation, and actual zero edge traces force all edge-carried
coefficients to vanish. The four cubic face indices and twelve quartic face
indices plus one interior index are classified structurally, without rank
enumeration. Actual monomial integrals give the compatibility conditions.
The defined source and zero-edge/zero-integral target spaces are proved
linearly isomorphic on every translated unit chain. Fixed linear quartic
and quintic velocity lifts solve the actual residuals on every positive
scale and have genuine gradient-energy bounds with a constant quantified
before translation, permutation, and scale. Global bubble assembly is
proved: strict barycentric positivity determines the actual integer cell
and unique sorted coordinate order, so every shared point of distinct
elements lies on a barycentric face of each. Every physical-boundary point
also lies on a face. The actual face-zero local maps therefore belong to
the defined global homogeneous conforming velocity space. Their energies
sum exactly with no mesh-dependent overlap factor. Combining them with
the mean-preserving skeleton map gives fixed uniformly stable right
inverses on the exact zero-element-mean pressure image for `N ≥ 2`.

The separate `N=1` right inverse is proved by finite-dimensional linear
sectioning. An injective actual pressure pullback into a finite product
of genuine reference `L²` spaces establishes finite dimensionality and
the true-energy bound for every fixed mesh. Its constant is allowed to
depend on that fixed mesh; this argument is used only for the single small
mesh, not to assert uniformity as `N` varies.

For each degree, the unrestricted discrete uniform-right-inverse target
is proved equivalent to a fixed
linear initial velocity lift matching every actual divergence element
mean, with one positive energy constant before all `N ≥ 2`. The
zero-element-mean inverse and the separate small mesh discharge every
other discrete composition step. The initial uniform mean lift follows
from the proved genuine continuous inverse and mean-preserving Fortin map.
The final unconditional theorems instantiate these composition results.

The physical Sobolev interface is proved on actual functions. True
indicator assembly gives an injective global `L²` pressure representative,
with squared norm equal to the genuine element-integral energy. The
geometry-only owner choice gives continuous zero-extended velocity
functions, agreeing with every incident polynomial even on shared faces.
Finite closed-convex gluing proves these functions globally Lipschitz.
Their actual gradients agree almost everywhere with the assembled
polynomial derivatives. Lipschitz integration by parts proves the defining
weak-derivative identities against every smooth compactly supported test
function; the derivatives are unique in `L²` and their energy is exactly
the defined velocity energy. A concrete smooth cutoff gives zero total
mean for every pressure in the actual divergence image.

Actual `H¹₀` membership is established by a proved smooth approximation,
not stipulated from pointwise boundary values. Normalized convolution is
composed with a small homothety about the cube center, compressing its
support into a closed box strictly inside the open cube. The derivative
formula follows by testing weak integration by parts against a reflected
bump and then using the actual chain rule. Common support and pointwise
bounds prove convergence of the function and all derivative components in
genuine squared `L²` error. `ConformingH1Zero.InH1ZeroCube` spells out the
standard weak-gradient plus smooth-closure criterion on actual functions;
it does not assert an additional identification with Mathlib's Fourier-
defined Bessel-potential Sobolev spaces.
Testing smooth weak integration by parts against `x_i u` and completing
the square proves an explicit cube Poincare estimate. The proved smooth
approximation transports it to every actual finite-element velocity:
complete genuine `H¹` energy is at most five times its gradient energy,
uniformly in mesh and degree. Thus the completed zero-element-mean right
inverses also have genuine uniform full `H¹` bounds.

The initial mean stage's polynomial flux identities are now derived from
actual integration. Arbitrary-exponent triangle integrals yield the
barycentric face functional; affine reconstruction identifies its chart
with each actual physical face. Polynomial differentiation, integration,
and scale transport prove Gauss identities on every actual tetrahedron,
with no degree restriction. The weights are orthogonal to face
displacements and point outward. The cubic face bubble has parameter
integral `1/120` on its own face and zero on the other three faces, so its
designated weighted face flux equals its actual divergence mean.
The genuine nonpolynomial weak traces and uniform initial mean lift use
the subsequent smooth-approximation and continuous-inverse arguments.

In particular, the mean and derivative formulas are now theorems about
actual polynomials and integrals, not definitions of coefficient-only
functionals. These results include actual macro conformity and uniform
physical macro lifting and mean-preserving edge/skeleton stages. The
assembled vertex and edge stages and their uniformly stable composition
with the final element bubbles are proved on the zero-element-mean
pressure image, with the mesh ranges stated above. Composing with the
initial mean lift proves the full divergence right-inverse bound.

## Mathematical interfaces

| Modules | Checked role |
| --- | --- |
| `PolynomialCalculus`, `BernsteinPolynomial` | Actual differentiation, substitution, and Bernstein coefficient calculus |
| `ChainGeometry`, `SkeletonBubble`, `VertexJetAlgebra`, `EdgeBubble`, `PolynomialSkeletonTrace` | Barycentric geometry, analytic edge-jet reconstruction, and local skeleton traces |
| `PolynomialIntegration`, `BetaPolynomialIntegral`, `BernsteinNestedIntegral`, `ReferenceChainMeasure`, `BernsteinVolumeIntegral` | Fundamental theorem of calculus through genuine reference tetrahedron integration |
| `ChainMeasureTransport`, `BernsteinMean` | Translation/permutation transport and divergence means |
| `QuarticBernstein`, `QuarticPolynomial`, `QuarticSpatial`, `QuarticVolume` | Physical control points through actual real polynomials, edge traces, and volume mean matrix |
| `QuarticNodalRealization`, `QuarticMacroConformity`, `QuarticReferenceLift` | Global nodal-product realization, all-point conformity, rectangular zero trace and a fixed genuine-energy-bounded reference mean inverse |
| `LatticeAffineTransport`, `PhysicalMacroFields`, `QuarticPatchCoverage`, `PhysicalMacroLift` | All-origin affine lattice transport, actual velocity-space membership, exact twelve-owner physical coverage, zero nonowner polynomials, all-edge protection and uniform physical macro lifting |
| `QuarticMacro`, `EdgeIncidence`, `RealTransport` | Exact finite algebra and scalar transport |
| `ScaledChainGeometry`, `PolynomialScaling` | Actual spatial and integral scaling |
| `PolynomialDegree`, `PolynomialL2`, `PolynomialL2Space`, `PolynomialInverseEstimate` | Genuine local volume norm, fixed-degree bounds, and uniform scaled vertex inverse estimate |
| `EdgeJetContinuity` | Common and zero edge jets from actual polynomial traces on closed segments |
| `FreudenthalMesh`, `MeshCoverage`, `MeshSegments` | Arbitrary-size mesh, conforming polynomial data, exact divergence image, cube coverage, and closed edges |
| `GridNodal`, `GridNodalSupport`, `NodalMesh`, `ConformingSkeletonBubble`, `SkeletonField` | Global nodal realization, arbitrary lattice support, and conforming nodal-product velocity fields |
| `ConformingEdgeJets`, `PressureVertexBound` | Vertex-divergence reconstruction from actual common/boundary-zero jets and uniform control of all pressure incidences |
| `FaceBubbleMean`, `MeanRoutingAlgebra` | Actual single-element face-transfer normalization and fixed connected-graph mean-routing algebra and norm bound |
| `HomogeneousBarycentric`, `HomogeneousSkeletonCompleteness`, `LowDegreeBubbleIndices`, `LowDegreeBubbleExpansion`, `AffineBarycentric` | Complete actual pressure representation, geometric edge/coefficients equivalence, structural low-degree indices, mean identities, and affine reconstruction |
| `ElementBubbleAlgebra`, `ElementBubbleLift`, `ElementBubbleInjectivity`, `ElementBubbleRange` | Explicit analytic inverses and a linear isomorphism between the actual local source and residual spaces |
| `PolynomialChainTransport`, `StableElementBubbleLift` | Orthogonal chain transport and actual quartic/quintic residual lifting with a geometry- and scale-independent energy constant |
| `VertexStarCoverage`, `VertexStarTypes`, `VertexStarSymmetry`, `VertexEdgeCoverage` | Exact arbitrary-`N` vertex/subchain coverage, boundary words, six valences, canonical edge counts, and geometric symmetry/active-boundary transport |
| `VertexStarConnectivity`, `VertexStarGraphTransport`, `ActualVertexStarGraph` | Explicit kernel-checked trees and graph isomorphisms proving actual geometric face connectivity of every vertex star |
| `VertexFaceGeometry`, `ActualFaceSupport`, `ActualFaceConformity`, `ActualFaceMean` | Exact two-owner geometry and actual supported cubic face fields, physical boundary values, paired means, and all vertex protections |
| `VelocityEnergy`, `StableFaceTransfer`, `StarMeanRouting`, `StableStarMeanRouting` | Pointwise-to-integrated finite-sum estimates, uniform `h^{-3}` transfer energy, and stable actual fixed linear mean routing on every vertex star |
| `RawVertexMean`, `FiniteLinearLifting`, `VertexCompatibility`, `VertexMeanCancellation` | Actual raw nodal means, finite-family fixed bounded operators, a differentiated compatibility map, and kernel-checked cancellation over all boundary words |
| `RawVertexField`, `RawVertexTrace`, `ActualRawVertexMean`, `MeanPreservingVertexLift` | Actual arbitrary-mesh conforming cubic fields, their precise traces, zero total means, and fixed mean-preserving supported correction |
| `ConformingVertexCompatibility` | Complete equality of actual divergence-vertex and compatibility images, including all boundary-edge constraints and a conforming cubic converse |
| `StableRawVertexField`, `StableVertexLift` | Uniform genuine gradient-energy bounds for raw fields, routed means, and fixed local vertex lifts |
| `BoundedOverlapEnergy`, `GlobalVertexLift` | Pointwise-to-integrated overlap estimate and a complete linear, zero-element-mean, uniformly stable vertex stage on every positive mesh size |
| `ConformingFaceModes`, `FaceModeTraces`, `ActualFaceEdgeTraces` | Actual conforming weighted face fields, all vertex protections, and full target/spill/other-edge trace identities |
| `FaceJumpCompatibility`, `BoundaryEdgeCompatibility`, `CheckerboardCompatibility` | Gradient jumps from actual conformity, boundary conormals, equal-pair/zero-source implications, and analytic four-sector checkerboard compatibility with explicit geometry hypotheses |
| `ActualEdgeCoverage`, `CanonicalEdgeCoverage` | Exact actual incidence equivalence and complete seven-type geometric coverage, including endpoint exchange in central inversion and uniform valence bound |
| `HomogeneousEdgeModes`, `EdgeModeUnisolvence`, `ActualPressureEdgeModes`, `StableEdgeCoefficients`, `EdgePressureData` | Complete actual edge coefficient extraction/decomposition, coefficient compatibility, and uniformly scaled true-volume data bounds |
| `OrderedEdgeGeometry`, `ActualOrderedEdgeGeometry`, `CanonicalSourceGeometry`, `ActualCanonicalSource`, `ActualCanonicalData` | Actual ordered incidences, all changing boundary tags, discharged canonical source geometry, and compatible actual pressure coefficient vectors |
| `CanonicalFacePatterns`, `CanonicalFaceTraceAlgebra`, `CanonicalPatternSpan` | Geometry-derived coefficients on all lattice states and explicit integer/real inverses on the exact source spaces |
| `UniversalFaceEdgeTrace`, `ActualCanonicalFaces`, `ActualCanonicalPatternTrace`, `ConformingNodalMultiplication` | Actual conforming primary/borrowed face realization, whole-edge traces, and quintic modes by global nodal multiplication |
| `ActualCanonicalEdgeLift`, `CanonicalEdgeProtection` | Fixed actual quartic/quintic canonical maps, whole-pressure-edge matching, protected vertex derivatives, and zero off-target divergence traces |
| `StableWeightedFaceField`, `StableCanonicalPattern`, `StableCanonicalEdgeLift` | Genuine weighted-face energy scaling and uniform whole-mesh energy bounds for both complete canonical maps |
| `CubeMeshSymmetry`, `CubePolynomialTransport` | Actual cube/mesh symmetries, affine derivative and divergence transport, conformity, true-energy and element-mean preservation |
| `CanonicalEdgeOrientation`, `CubeTraceTransport` | Canonical reduced boundary locations, exact actual edge-incidence transport and endpoint exchange, full traces and local pressure-energy transport |
| `CanonicalPressureLift`, `CanonicalLiftSupport`, `UniformEdgeLift` | Fixed actual pressure-to-velocity edge maps in both degrees, full protected traces, endpoint-star polynomial support and uniform edge-star integral bounds |
| `EdgeAssemblyGeometry`, `GlobalEdgeLift` | Exact six-fold incidence counting, fifty-six-fold overlap and simultaneous uniformly stable global edge-jet correction |
| `DivergenceEnergy`, `GlobalSkeletonLift` | Actual residual/divergence integral bounds and uniformly stable combined vertex/edge skeleton lifting on the exact pressure image |
| `MacroPatchAdjacency`, `MacroMeanTransfer`, `CubeClusterGraph` | Actual arbitrary-mesh two-cube transfers, exact mean differences, edge protection, supported element graphs and proved connectedness |
| `CubeClusterRouting`, `StableCubeClusterRouting`, `RectangularCubeCluster`, `EdgeRoutingBox` | Fixed linear cluster routing, uniform physical energy, structural rectangular connectivity and bounded actual edge boxes |
| `ElementMeanEnergy`, `ClusterMeanRemoval` | Genuine mean-square estimates and uniformly stable fixed mean removal preserving full edge traces |
| `BarycentricMonomialMean`, `WeightedFaceMean`, `BilinearFaceMean`, `DivergenceMean`, `CanonicalLiftMean`, `ZeroTotalEdgeLift` | Actual monomial derivative integrals, paired weighted-face means, symmetry transport and zero total mean of every local edge lift |
| `MeanPreservingEdgeLift`, `EdgeRoutingOverlap`, `GlobalMeanPreservingEdgeLift`, `MeanPreservingSkeletonLift` | Mean-free local maps, 875-fold geometric overlap, global mean-preserving edge and skeleton lifting for `N ≥ 2` |
| `MeshIntersectionFaces`, `MeshMeasurePartition` | Structural face containment, proper affine face planes and true pairwise almost-everywhere element disjointness |
| `ElementBubbleAssembly`, `GlobalElementBubbleLift`, `ZeroElementMeanRightInverse` | Actual all-point conforming global bubble lifting and the uniformly stable zero-element-mean right inverse for both degrees |
| `FixedMeshRightInverse`, `UniformMeanLiftReduction` | True-energy fixed-mesh and `N=1` inverses; exact equivalence of the unrestricted uniform target with the initial mean-lift statement |
| `GlobalPolynomialL2`, `ConformingVelocityFunction`, `ClassicalVelocityGradient` | Injective genuine global L2 representatives, continuous conforming zero extensions and actual almost-everywhere classical gradients |
| `FiniteClosedIntervalGluing`, `FiniteClosedConvexGluing`, `ConformingVelocityLipschitz`, `WeakVelocityGradient`, `ConformingDivergenceMean` | Lipschitz gluing, genuine weak integration by parts, exact weak-gradient energy and zero total mean of the actual pressure image |
| `WeakGradientMollification`, `MollificationL2`, `BoundedMeshFunctions`, `InteriorMollification`, `InteriorMollificationL2`, `ConformingH1Zero` | Proved weak-gradient convolution, L2 approximation, strict interior support and actual H1_0 membership by smooth closure |
| `SmoothCubePoincare`, `ConformingH1Energy` | Explicit cube Poincare estimate, uniform full actual H1-energy control and full-H1 stable zero-element-mean inverses |
| `TriangleBernsteinIntegral`, `BarycentricFaceIntegral`, `BarycentricPolynomialGauss`, `BarycentricFaceGeometry` | Genuine triangle integration, actual spatial face charts and arbitrary-degree polynomial Gauss identities |
| `ScaledFaceGauss`, `FaceFluxNormalization` | Every-mesh physical face charts, outward flux weights, actual divergence/face identities and exact cubic single-face flux normalization |
| `ChainFiberIntegration`, `SmoothChainGauss`, `SmoothFaceTrace`, `SmoothChainTransport`, `ScaledSmoothCalculus` | Genuine C1 Gauss formulas from coordinate-fiber FTC; actual affine transport and explicit physical face estimates with constant six |
| `WeakFaceTrace`, `H1ApproximationL2`, `WeakFaceGauss` | Actual L2 face limits independent of H1 approximation; local L2 convergence, weak trace bounds and genuine weak element flux identities |
| `FaceL2MeanEstimate`, `WeakFaceFluxCorrection`, `BoundaryWeakFaceTrace` | Exact triangle area, actual weak normal-flux bounds, fixed linear conforming cubic corrections with exact paired means and scale-explicit residual energy; zero weak traces on every inactive grid boundary face |
| `WeakGradientLinearity`, `H1ApproximationLinearity`, `WeakLinearFaceTrace`, `ConformingWeakFaceTrace` | Proved linear weak-gradient/H1-approximation structures, one fixed linear weak trace operator and genuine codimension-one L2 identification with actual finite-element polynomial face restrictions |
| `IntervalH1Estimate`, `BoxH1Estimate`, `WeakBoxH1Estimate`, `TranslatedBoxH1Estimate` | FTC and Cauchy–Schwarz interval/box Poincare estimates, actual coordinate Fubini, and transport to genuine weak H1 data on every translated box |
| `BoundaryBoxH1Estimate`, `BoundaryHalfBoxGeometry`, `LocalAverageEstimates` | Actual H1_0 zero extension, structural half-box boundary estimates and nested-volume mean bounds without boundary-state enumeration |
| `LinearNodalInterpolation`, `VolumeNodalInterpolation`, `MeshAveragingBoxes` | One fixed linear actual conforming homogeneous P1 volume interpolant, with true nodal-box averages and arbitrary-N geometric containment |
| `BarycentricInterpolationEstimate`, `LocalVolumeInterpolation` | Explicit barycentric physical gradient bounds, local weak-H1 interpolation stability and genuine local L2 error of order h |
| `InterpolationBoxOverlap`, `StableVolumeInterpolation`, `VolumeInterpolationL2` | Structural 1296-fold overlap, uniform actual gradient stability, and true whole-space L2 error of order h for all positive N |
| `OrderedSharedFaceChart`, `InteriorFaceCoverage`, `FacePartner` | Identical actual shared-face charts, equal weak traces, opposite fluxes, unique arbitrary-N interior-face neighbors and a geometry-only partner involution with eight-incidence support counting |
| `VelocityH1Representation`, `InterpolationResidual` | A fixed linear actual finite-element weak-H1 representation, exact energy and polynomial flux identification, uniform residual gradient bound and zero boundary-face residual flux |
| `GlobalFaceCorrection`, `StableGlobalFaceCorrection`, `UniformMeanFortin` | Actual fixed linear cubic global correction, exact element means, uniform physical energy and the complete uniformly stable element-mean Fortin map on genuine H1_0 input |
| `CubeZeroMeanL2`, `ContinuousInverseReduction` | Actual mean-zero cube L2 pressure domain and mesh embedding; conditional transport of a genuine continuous cube divergence inverse to both full discrete targets, including N=1 |
| `H1ZeroLinearity`, `WeakH1ZeroCubeEnergy` | Actual H1_0 vector space, true Poincare estimate on every weak H1_0 input and full-H1 stability of the mean Fortin map |
| `WeakH1ZeroGradientSupport`, `BoundedWeakDivergence` | Actual cube-supported weak gradients with zero genuine total integrals; fixed bounded weak divergence into actual mean-zero cube L2 functions |
| `H1ZeroL2Jet`, `WeakGradientL2Closed`, `H1ZeroL2Closed`, `H1ZeroHilbertSpace` | Genuine value-and-gradient Hilbert norm, exact almost-everywhere-zero kernel, strong L2 closure of weak derivatives and H1_0 smooth approximations, and a closed complete Hilbert range |
| `H1JetRepresentative`, `CubePressureHilbert` | Fixed linear actual H1_0 representatives with exact energy; a closed complete mean-zero pressure Hilbert space and an onto actual-function class map with exact L2 norm |
| `HilbertLinearSection`, `HilbertCubeDivergence`, `HilbertInverseReduction` | Genuine bounded divergence between complete Hilbert spaces; orthogonal-kernel bounded linear sections and conditional transport of divergence surjectivity to both unrestricted discrete targets |
| `BogovskiiCubeGeometry`, `BogovskiiTruncation`, `BogovskiiSchwartzKernels` | Actual normalized central bump, coordinate moments, genuine truncated integrals and uniform interior support geometry |
| `EuclideanCoordinateTransport`, `NormalizedFourierDilation`, `GenuineL1L2Fourier` | Exact Euclidean Lebesgue/L2/partial-derivative transport, genuine normalized Fourier dilation, and agreement of actual L1 Fourier integrals with Hilbert L2 Fourier |
| `FourierDirectionalDecay`, `FourierRayBound`, `BogovskiiRayRescaling`, `WeightedIntegralSquare` | Genuine directional decay, actual integrable ray bounds, the exact small-scale substitution and weighted variance/Cauchy--Schwarz |
| `SmallScaleFourierKernel`, `RescaledFourierEnergy`, `FourierEnergyDilation`, `SmallScaleFourierL2` | Complete uniform lower-half Fourier-side L2 estimate, including all actual product integrability and Fubini obligations |
| `CompactParameterDifferentiation`, `C1CubeH1Zero`, `BogovskiiKernelDifferentiation`, `BogovskiiC1Truncation` | Genuine compact-parameter Frechet differentiation, C1 cube-supported H1_0 membership and actual C1/H1_0 truncated Bogovskii fields with their true derivative formula |
| `BogovskiiMixtureFourier`, `CompactFourierIntegration`, `CubeSupportedMixtures` | Actual affine-mixture Fourier identity, compact Fourier Fubini, continuity and uniform cube support |
| `SpatialLowerHalfL2`, `CubeSupportedL1L2`, `SpatialUpperHalfL2`, `ScalarMixtureEstimate`, `ScalarMixtureDifferentiation` | Uniform genuine scalar spatial derivative L2 estimate, including both scales and actual differentiation of the spatial formula |
| `EuclideanCubeTransport`, `BogovskiiPressureSchwartz` | Exact cube/compact-parameter volume transport, actual smooth pressure and moment inputs, and their genuine L2 energy bounds |
| `BogovskiiScalarIdentity`, `BogovskiiGradientEstimate` | Actual moment-kernel split, all nine true physical derivatives, and a complete truncation-independent actual gradient-energy bound |
| `BogovskiiKernelDivergence`, `BogovskiiTimeFTC`, `BogovskiiDivergenceIdentity` | Actual kernel time derivative, genuine FTC, complete truncated divergence identity and exact zero-mean compatibility |
| `BogovskiiPressureMixture`, `BogovskiiPressureConvergence` | True nonsingular mass-mixture formula and convergence of the actual pressure in genuine squared L2 error |
| `SmoothCubePressureSpace`, `SmoothCubePressureDensity` | Actual smooth mean-zero cube data, explicit normalized mean-corrected tests and proved density in the genuine pressure Hilbert space |
| `BogovskiiHilbertTruncation`, `BogovskiiHilbertConvergence` | Actual H1_0 Hilbert truncations, a fixed uniform norm bound, exact error-norm identity and genuine divergence convergence |
| `UniformApproximationSurjectivity`, `BogovskiiHilbertSurjectivity` | Uniform half-error preimages and the checked complete-space geometric-series proof of actual cube-divergence surjectivity |
| `MainTheorem` | Unconditional genuine continuous cube inverse and complete uniform discrete right inverses for k=4,5 on every N>=1 |
| `DiscreteInfSup` | Uniform reduced inf-sup witnesses with actual physical pairing, true seminorm/L2 denominator and strict positivity for every nonzero pressure |

`FreudenthalMesh.HasUniformRightInverse` states the discrete target with
the stability constant quantified before `N` and a single linear operator
on each mesh. `MainTheorem` proves this target in both degrees without
remaining hypotheses. Actual weak-gradient energy, the `H¹₀` smooth-closure
criterion and the uniform initial element-mean lift are proved. Its smooth and weak-H1
trace/flux foundations and the local cubic correction estimate are proved.
Stable interpolation is proved by an explicit fixed linear volume-averaging
construction, not an assumed Scott–Zhang theorem. Its actual gradient energy
is at most `373248` times the input weak-gradient energy, and its actual
whole-space squared L2 error is at most `995328 h²` times that energy.
Both constants precede every `N > 0`, and the interpolation map precedes
its input. Boundary faces, edges and corners are covered by structural
half-box estimates. Shared-face charts are identical in actual chain
order; unique genuine L2 traces give equal weak restrictions and opposite
outward fluxes. A geometry-only involution pairs the unique interior-face
owners. Eight-incidence support counting proves a uniform physical bound
for the actual fixed linear cubic correction. Its composition with
interpolation proves `UniformMeanFortin.uniform_mean_fortin`: one fixed
linear map on genuine weak H1_0 data preserves every actual element
divergence integral with a constant before every positive N.

The actual weak H1_0 data form a proved real vector space. Strong L2
convergence of the value and all weak derivatives preserves both the
defining integration-by-parts identities and the interior smooth-closure
criterion; a genuine diagonal approximation proves the latter. The
value-and-gradient map into four actual L2 classes has squared norm
exactly the full H1 energy and kernel exactly the almost-everywhere-zero
data. Its range is closed and complete. The actual weak gradients vanish
outside the cube almost everywhere and have zero genuine global
integrals. Their divergence is a fixed bounded linear map into actual
mean-zero cube L2 functions. Boundedness and completeness do not assert
that this divergence map is onto.
Cube-supported pressure classes form a proved closed complete Hilbert
subspace: support is a bounded-indicator fixed-point condition and zero
mean is the kernel of pairing with the cube indicator. Actual pressure
functions map onto it with exactly their genuine L2 energy. A fixed
linear section selects actual H1_0 representatives of every velocity
jet with exactly its full H1 norm. The resulting divergence is a genuine
bounded linear Hilbert operator. Its proved surjectivity gives a
bounded linear section by projection off the closed kernel and the
Banach inverse theorem. The checked actual-function transport connects
that section to both full discrete targets, with the input and mesh
quantifiers in the required order. The surjectivity proof uses the actual
uniformly bounded approximations and a complete-space geometric series.

The continuous construction uses the standard Bogovskii integral with a
fixed normalized central smooth bump. Its true support geometry is proved
for all cube faces, edges and corners by coordinate convexity, and every
positive truncation has compact support strictly inside the cube. The
actual truncated integral is C1, its Frechet derivative is the proved
compact-parameter integral, and its H1_0 membership follows from actual
smooth approximation. No C-infinity or boundary assertion is inferred
from the kernel's formal expression alone.

The elementary Fourier L2 route of [Durán, Section 2](https://arxiv.org/abs/1103.3718)
has a checked lower-half estimate: directional Fourier differentiation
gives quadratic decay; the actual weighted ray integral is bounded by
`pi * (L1 norm of the kernel + L1 norm of its second directional derivative)`.
The genuine substitution `s=t/(1-t)`, weighted Cauchy--Schwarz, exact
three-dimensional volume scaling, proved product integrability, Fubini
and Plancherel give a lower-half Fourier energy bound independent of
the truncation. Measure-preserving Euclidean transport and the actual
L1/L2 Fourier identification connect the analytic interfaces precisely.
The genuine scalar spatial mixtures now have the exact Fourier identity,
true compact Fourier Fubini, actual support and both lower/upper-half L2
bounds. Genuine differentiation of their compact-parameter spatial formula
identifies its directional derivative with the estimated time integral.
Actual smooth pressure and moment data have exact L2 transport and no-
larger moment energy. The true moment-kernel split identifies the scalar
formulas with the actual vector truncations. All nine physical derivatives
and their complete truncation-independent actual gradient-energy bound are
proved. Actual kernel-time differentiation and FTC give the complete
truncated divergence identity, and the true zero input mean cancels the
normalized-bump term. The nonsingular pressure-mixture formula and dominated
convergence prove genuine L2 convergence of these divergences. Actual
smooth mean-zero pressures are dense: orthogonality to explicit mean-
corrected tests forces a representative to be constant in the open cube,
whose boundary has zero volume, and zero mean forces that constant to
vanish. Uniform bounds and density provide half-error preimages with one
fixed norm constant. The complete-space geometric-series theorem yields
actual divergence surjectivity; mere density is not used as a substitute.

`MainTheorem.continuous_cube_right_inverse` proves
`ContinuousInverseReduction.HasContinuousCubeRightInverse`: one fixed
linear inverse on actual zero-extended mean-zero L2 data, with genuine
H1_0 outputs and a uniform true-gradient bound. The quartic and quintic
final theorems instantiate the proved transport, mean lift and discrete
composition, including N=1. No missing theorem is represented by a project
axiom. [FORMALIZATION_PLAN.md](FORMALIZATION_PLAN.md) records the completed
scope; higher degrees and an identification with Fourier-defined Bessel-
potential Sobolev spaces are not asserted.

## Toolchain and dependencies

- Lean 4.33.1, pinned by `lean-toolchain`;
- Mathlib 4.33.1 and all transitive revisions, pinned by `lakefile.toml`
  and `lake-manifest.json`;
- elan with `lake` available on `PATH`.

No CAS, SMT solver, or Python package is required for the Lean proofs.
From the repository root, reproduce the complete check with:

```sh
cd lean
lake exe cache get
bash scripts/verify.sh
```

`lake exe cache get` downloads the standard Mathlib dependency cache; the
project's own proofs are built from the supplied source. To run the two
checks separately from this directory:

```sh
scripts/lakew build
scripts/lakew env lean FreudenthalSVLean/TrustAudit.lean
```

The combined reproducibility check is `bash scripts/verify.sh`.

The wrapper uses a project-local elan installation when present, otherwise
the ordinary `lake` on `PATH`; it does not modify user shell configuration.
The root module imports every mathematical module, so a full
build includes the new calculus, integration, scaling, and mesh proofs.
`TrustAudit.lean` prints principal theorem dependencies and checks every
declaration in the project namespace against the three standard logical
axioms. It fails on project-defined or otherwise nonstandard axioms.

## Manuscript provenance and license

The manuscript source snapshot used for the formalization has SHA-256
`1a6e5b0b5cde8f0a180c35e418b5b6d37f4db635cfb7811b11f8f6844c4bab48`.
The corresponding publication-source snapshot has SHA-256
`666a0e96c4523fbef3e68cd62a65f086d20aabe2b8cb01c4f98d4722cbf97649`.

Neither snapshot is needed to build this directory. Mathematical references
in the source identify the relevant theorem, lemma or displayed formula.
All original contents in this directory are distributed under
`GPL-3.0-or-later`, the same license as the repository; see [LICENSE](../LICENSE).
