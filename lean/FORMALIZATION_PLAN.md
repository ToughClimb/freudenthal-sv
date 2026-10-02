# Formalization plan

All required items for the complete `k=4,5`, every-`N≥1` uniform
right-inverse proof are checked. The final unconditional theorems are
`MainTheorem.quartic_uniform_right_inverse` and
`MainTheorem.quintic_uniform_right_inverse`. The higher-degree extension
and identification with Fourier-defined Bessel-potential Sobolev spaces
are not claimed. Reproduce with `bash scripts/verify.sh`.

## Phase 1 — finite exact algebra

- [x] Encode the quartic macroelement's 11 by 11 scaled mean matrix.
- [x] Give a kernel-checkable rational two-sided inverse certificate.
- [x] Prove that the determinant is nonzero from that certificate.
- [x] Prove exact spanning of the equal-pair and checkerboard incidence spaces.
- [x] Encode the eleven Bernstein fields on the twelve-tetrahedron two-cube
      patch and prove that every edge-carried cubic divergence coefficient,
      and hence every encoded Bernstein edge restriction, vanishes.
- [x] Reconstruct the first eleven element means from the displayed physical
      control points and prove that the resulting scaled matrix is exactly
      the independently encoded paper matrix `A`.
- [x] Strengthen the matrix certificate from nonzero determinant to the exact
      paper value `det A = -6` using the proved-correct Bird algorithm.
- [x] Transport the matrix inverse, determinant, equal-pair span, and
      checkerboard span from `ℚ` to `ℝ`.
- [x] Derive the encoded Bernstein differentiation formula generically from
      `MvPolynomial`, rather than taking the standard coefficient identity as
      the definition of the finite calculus.
- [x] Formalize the simplex integration identity underlying the encoded
      Bernstein mean formula.
- [x] Identify polynomial differentiation with actual real Fréchet derivatives.
- [x] Prove zero actual real edge restriction of each displayed quartic field.
- [x] Prove that actual Lebesgue volume means of the displayed fields equal
      the exact coefficient records, and hence the matrix `A/30`.

## Phase 2 — local polynomial constructions

- [x] Formalize barycentric product differentiation on a reference tetrahedron.
- [x] Prove cubic vertex-bubble jets and zero vertex jets of face bubbles.
- [x] Prove analytic barycentric duality and full derivative reconstruction
      from issuing edge jets; construct the fixed linear cubic correction
      and prove protection of every other tetrahedron vertex.
- [x] Verify local endpoint and middle quintic edge-bubble derivative traces.
- [x] Construct the actual globally conforming weighted face modes, including
      degree bounds, homogeneous physical boundary values, two-owner support,
      all vertex protections, and complete target/spill/other-edge traces.
- [x] Prove complete homogeneous edge expansions in every degree; apply them
      to actual physical pressure polynomials and extract their coefficients
      with one fixed linear map. Prove the cubic/quartic zero-endpoint modes.
- [x] Recover the mode coefficient vectors from interior values in an
      arbitrary real vector space, and transfer pointwise linear-subspace
      compatibility to all coefficients without a rank assumption.
- [x] Prove protected traces from repeated or missing barycentric factors.
- [x] Prove actual single-tetrahedron face-bubble divergence means,
      unit-mean vector normalization, and all vertex protections.
- [x] Prove exact two-tetrahedron support, conformity, physical boundary
      values, paired actual means, global vertex protection, and a uniform
      whole-mesh `h^{-3}` energy bound for interior star-face transfers.
- [x] Verify canonical borrowed-face constructions on the actual arbitrary-size
      mesh, both owners' boundary admissibility, full off-target edge
      cancellation, and protected vertex derivatives.
- [x] Prove explicit integer/real incidence inverses on the exact canonical
      source spaces, compatible actual pressure coefficients, and fixed
      linear quartic/quintic canonical edge lift maps.
- [x] Derive quintic endpoint/middle modes by actual global nodal
      multiplication and the polynomial product rule.
- [x] Prove genuine weighted-face energy scaling and uniform whole-mesh
      bounds for both degrees' complete canonical incidence lift maps.
- [x] Construct homogeneous barycentric representations from actual spatial
      polynomials and prove both directions of the geometric edge/coefficients
      condition, with structural classification of the low-degree indices.
- [x] Formalize the degree-four and degree-five element-bubble source/target
      isomorphisms on translated unit chains, including inclusion,
      injectivity, and explicit surjectivity with genuine integral compatibility.
- [x] Prove fixed linear quartic/quintic residual lifts on all positive-scale
      chains, their degrees and face protections, and actual gradient-energy
      bounds independent of permutation, translation, and scale.
- [x] Realize every displayed macro Bernstein term as a fixed normalized
      global nodal product. Prove its polynomial restrictions from an exact
      integer/natural node certificate and the generic monomial formula.
- [x] Prove all-point conformity, degree bounds, and full rectangular
      exterior zero trace of the actual quartic macro fields.

## Phase 3 — mesh combinatorics and transport

- [x] Define translated, coordinate-permuted, scaled chain tetrahedra.
- [x] Prove actual barycentric values, gradients, and partition of unity.
- [x] Prove genuine volume integral transport and `h^3` scaling.
- [x] Prove mean preservation and `h^{-3}` squared gradient-energy scaling
      of the macro amplitude `h^{-2}`.
- [x] Define arbitrary-`N` conforming polynomial velocity data, its exact
      divergence image, and real-integral energies.
- [x] Prove coverage of exactly the cube for every `N ≥ 1`.
- [x] Prove tetrahedron convexity, actual vertex membership, and containment
      of closed geometric edge segments, including boundary endpoints.
- [x] Identify a globally continuous nodal function with its local polynomial
      data on all integer-lattice tetrahedra, prove zero restriction on every
      nonincident tetrahedron, and transport it to arbitrary `N`.
- [x] Prove actual velocity-space membership, support, homogeneous boundary
      values, and other-vertex protection of quadratic/cubic endpoint products.
- [x] Prove conformity, degree, support, and homogeneous boundary values for
      arbitrary fixed nodal-product exponents under an explicit geometric
      boundary-plane criterion.
- [x] Prove tetrahedron intersection geometry and almost-everywhere disjointness.
- [x] Parameterize every actual vertex incidence on every positive `N` by
      twenty-four universal states, prove boundary-tag admissibility, and
      classify all boundary words by coordinate permutations and inversion.
- [x] Prove the six vertex valences, canonical incident/active edge counts,
      actual subchain coverage, and geometric symmetry/active-boundary transport.
- [x] Prove connectedness of every actual vertex-star face graph by explicit
      kernel-checked canonical trees and proved geometric graph isomorphisms.
- [x] Prove exact arbitrary-mesh edge/catalog incidence equivalence, seven
      positive directions, boundary-word valences, and the six-element bound.
- [x] Prove exhaustive geometric classification of the seven edge-incidence
      types by equality of full tetrahedron vertex sets under coordinate
      permutation and central inversion with correct endpoint exchange.
- [x] Transport shared-face, containing-boundary-plane, and borrowed-face
      neighbor data to actual ordered canonical edge lifting constructions
      for every positive mesh size and all changing endpoint tags.
- [x] Transport canonical compatibility and lift operators under arbitrary
      coordinate permutations and central inversion with endpoint exchange,
      including conformity, boundary values, and energy.
- [x] Prove support, boundary trace, global conformity, and local-star
      geometric classification for vertex and edge skeleton fields on
      arbitrary `N`.
- [x] Prove actual affine transport of all lattice nodal polynomials,
      divergence, volume integrals and gradient energies. Identify all twelve
      owners of any admissible physical two-cube patch, for every integer
      origin and coordinate order, and prove zero polynomial on all nonowners.

## Phase 4 — analytic and global theorem

- [x] Prove positive definiteness of the actual reference polynomial `L²`
      norm and construct its injective `Lp` representation.
- [x] Prove fixed-degree linear-map and derivative integral bounds and the
      `h³ |r|_T(a)|² ≤ C(d) ∫_T r²` vertex inverse estimate, with the constant
      quantified before all geometry and scale parameters.
- [x] Prove common directional jets from common closed-edge traces and
      zero directional jets from zero closed-edge traces.
- [x] Derive common and boundary-zero jets from the actual conforming velocity
      definition and prove the physical vertex-divergence reconstruction.
- [x] Derive conormal gradient jumps directly from conformity at arbitrary
      common face points. Derive boundary conormals and prove equal-pair,
      zero-source, and checkerboard implications with explicit face geometry
      and independent-conormal hypotheses.
- [x] Prove actual edge-star pressure data decompositions, transfer any
      pointwise linear compatibility subspace to their coefficients, and
      bound their squares in genuine incident-element volume norms with
      a constant before all mesh and edge parameters.
- [x] Prove the pressure degree bound from the exact divergence-image
      definition and the summed arbitrary-`N` pressure-vertex data estimate.
- [x] Construct a fixed linear zero-sum mean right inverse on any connected
      finite dual graph with normalized face transfers, with an explicit
      graph-size norm estimate.
- [x] Discharge the actual vertex stars' connectivity and transfer hypotheses,
      construct their fixed linear supported cubic mean-routing operators,
      and prove preservation of all vertex rows and a uniform physical
      `energy ≤ C h^{-3} sum m_T^2` estimate for every positive `N`.
- [x] Derive actual local means of raw cubic vertex edge-jet fields and
      prove fixed bounded exact-image inverses for finite linear-map families.
- [x] Connect the actual compatibility maps to the finite-family inverse
      theorem and prove raw-field mean cancellation on complete active edge stars.
- [x] Discharge two-cube transfer geometry for arbitrary actual face-adjacent
      cubes; prove connectivity and size bounds for fixed rectangular edge
      clusters containing at most 27 cubes and 162 tetrahedra, including all
      boundary configurations and every `N ≥ 2`.
- [x] Build actual global L² representatives and continuous conforming zero
      extensions. Prove Lipschitz gluing, genuine distributional weak partial
      derivatives, their L² uniqueness and exact weak-gradient energy.
      Prove zero total mean of every pressure in the actual divergence image.
- [x] Prove actual H¹₀ membership by the standard smooth-closure criterion:
      construct smooth convolutions with support compressed strictly into
      the open cube, prove their derivative formula from weak integration
      by parts and prove convergence of all function/derivative L² errors.
      This does not identify Fourier-defined Bessel-potential Sobolev spaces.
- [x] Prove an explicit cube Poincare estimate by weak integration by parts
      and smooth approximation. Bound genuine complete H¹ energy by five
      times gradient energy, uniformly in all meshes and degrees, and give
      the zero-element-mean inverse its complete H¹ stability bound.
- [x] Prove complete vertex compatibility from continuous edge jets, including
      all physical boundary constraints and an actual conforming cubic converse.
- [x] Construct the fixed linear vertex lift, including all boundary states,
      preservation of every element mean, and uniform actual gradient-energy
      estimates; assemble the full vertex stage with the four-field overlap
      bound and exact counting of all tetrahedron--vertex incidences.
- [x] Prove canonical edge compatibility from actual conformity, all
      primary/borrowed face constructions, whole-pressure-edge matching,
      protection of all mesh vertex derivatives and off-target edge traces,
      and uniformly bounded canonical lift maps.
- [x] Complete arbitrary-orientation edge transport, including actual
      boundary tags, endpoint exchange, every protected trace, physical
      energy and endpoint-star polynomial support.
- [x] Assemble one global edge-jet operator in each degree with exact six-fold
      pressure incidence counting and a fifty-six-fold field overlap bound.
- [x] Compose the vertex and edge stages on the exact divergence image;
      prove residual membership, zero full edge traces and one uniform
      actual integral energy bound for each fixed linear skeleton lift.
- [x] Preserve every required element mean on fixed supported patches for
      `N ≥ 2`: prove zero total mean of every actual local edge map by genuine
      weighted-face integrals, remove its element means without changing any
      full edge trace, and assemble a fixed mean-preserving skeleton lift.
      Its residual has exactly the input element means.
- [x] Prove the fixed quartic reference mean inverse's genuine gradient
      bound, with actual conformity, complete boundary trace and all-edge
      protection. Transport its actual means and energy to every physical
      two-cube patch and prove one constant before all meshes and patches.
- [x] Construct fixed geometric cube-cluster mean-routing operators and prove
      connectivity, linearity, exact actual means, edge protection, bounded
      cluster sizes and uniform physical energy. All geometric choices precede
      the input field. Actual mean-square bounds cancel the scaling factor.
- [x] Prove a genuine integrated bounded-overlap estimate and discharge its
      geometric hypotheses for the complete arbitrary-mesh vertex stage.
- [x] Prove bounded overlap and uniform energy for the full edge-jet assembly.
- [x] Prove the 875-fold actual routing-neighborhood overlap and the uniform
      global mean-preserving edge/skeleton bounds for both degrees on every
      `N ≥ 2`.
- [x] Assemble the final element bubbles and prove their global conformity,
      boundary values and energy bound; compose a stable right inverse on
      the exact image with zero element means for every `N ≥ 2`. Structural
      strict-cell and sorted-order uniqueness prove actual intersection
      face containment; proper affine face planes prove almost-everywhere
      mesh disjointness without an intersection catalogue.
- [x] Complete the small-mesh `N=1` case using a finite-dimensional linear
      section and proved actual pressure/gradient integral bounds. The
      fixed-mesh constant is not asserted to be uniform as `N` varies.
- [x] Prove that the unrestricted discrete uniform target in each degree is
      equivalent to a fixed linear initial element-mean lift with one energy
      constant before every `N ≥ 2`; discharge residual membership, true means,
      full divergence recovery, all energy compositions and the small mesh.
- [x] Prove the initial stable element-mean lift from the genuine continuous
      cube inverse and mean-preserving Fortin map, then instantiate the
      complete unrestricted divergence right inverse.
- [x] Derive actual arbitrary-exponent triangle and barycentric face
      integrals; identify charts with actual spatial tetrahedron faces;
      prove arbitrary-degree polynomial Gauss identities and exact physical
      scale transport for every positive mesh size. Prove outward signs,
      face-displacement orthogonality and cubic single-face normalization.
- [x] Prove genuine C1 Gauss formulas by coordinate-fiber FTC, true affine
      transport, and explicit physical face trace estimates with constant six.
- [x] Construct actual L2 face limits for every function with a genuine
      smooth H1 approximation; prove existence, uniqueness, independence of
      approximation, physical weak face bounds and actual weak element flux
      identities. Prove zero weak H1_0 traces for all inactive grid faces from
      their actual lower/upper coordinate planes, without a boundary catalogue.
- [x] Prove exact parameter-face measure and a true weak normal-flux bound;
      connect it to the fixed linear cubic conforming two-owner correction,
      its exact paired means and a uniform local bound by
      `6 h^{-2} value-residual energy + gradient-residual energy`.
- [x] Prove linearity of actual weak gradients and smooth H1 approximation;
      construct one fixed linear face-trace operator before its input.
      Identify finite-element weak traces with the true polynomial face
      restrictions by genuine codimension-one L2 convergence, not volume
      almost-everywhere equality.
- [x] Prove a fixed linear actual homogeneous P1 volume-averaging
      interpolant on genuine weak H1_0 data. Derive interval and box
      Poincare estimates from FTC/Fubini, pass to weak data, and cover all
      boundary configurations by half-box geometry. Explicit barycentric
      estimates and a structural 1296-fold overlap bound prove uniform
      gradient stability and actual whole-space L2 error of order h for
      every N > 0. The constants precede N and the map precedes its input.
      This supplies the needed interpolation estimates without importing
      a Scott–Zhang theorem.
- [x] Complete shared-face chart/trace compatibility: actual increasing
      face-node orders and triangle charts agree pointwise, genuine weak
      traces agree, and outward fluxes are opposite. Prove the unique
      second owner and index on every interior face for every N>0, and
      a geometry-only partner involution before its input.
- [x] Assemble the actual fixed linear cubic face correction, prove its
      exact element means, eight-incidence polynomial support bound and
      uniform physical energy. Compose it with volume interpolation to
      prove a complete uniformly stable element-mean Fortin map on
      genuine H1_0 input for every N>0, including boundary elements.
- [x] Define the exact actual-function continuous cube inverse obligation;
      prove mean-zero actual L2 pressure embedding and every conditional
      composition from that obligation to the unrestricted k=4,5 targets,
      including the separate N=1 case. Existence of that continuous
      inverse is not asserted by these conditional results.
- [x] Prove linearity of the actual H1_0 smooth-closure criterion, true
      Poincare control for every weak H1_0 function, almost-everywhere
      cube support and zero genuine global integrals of weak derivatives,
      and bounded actual divergence into the zero-mean cube L2 domain.
- [x] Construct the genuine L2 value-and-gradient Hilbert map with exactly
      the full H1 energy and almost-everywhere-zero kernel. Prove strong
      L2 closure of weak derivatives and H1_0 smooth approximations,
      and hence closedness and completeness of the actual Hilbert range.
- [x] Prove the closed complete Hilbert space of mean-zero cube L2
      pressures and the onto actual-function class map with exact norm.
      Construct fixed linear actual H1_0 jet representatives with exact
      energy and genuine bounded divergence between the Hilbert spaces.
- [x] Prove bounded linear sections of surjective Hilbert operators via
      orthogonal kernel projection and the Banach inverse theorem.
      Transport genuine cube-divergence surjectivity conditionally to
      the actual-function inverse and both full discrete targets.
- [x] Construct the actual normalized central Bogovskii bump, prove its
      true integral and interior support, and derive the actual kernel's
      convex support geometry for all boundary configurations. Define
      genuine iterated truncated integrals and their exact kernel split.
- [x] Prove measure-preserving Euclidean coordinate transport with exact
      actual L2 norms and partial derivatives. Construct the actual bump
      and coordinate moments as compactly supported Schwartz kernels.
- [x] Prove quadratic directional Fourier decay, actual integrability and
      uniform ray bounds, and the genuine substitution s=t/(1-t). Derive
      weighted Cauchy--Schwarz from the true weighted variance integral.
- [x] Complete the uniform lower-half Fourier-side L2 bound, including
      all actual product integrability, genuine Fubini, exact 3D dilation
      and Plancherel. This item alone is a Fourier-side estimate, not a
      complete Bogovskii H1 bound.
- [x] Identify actual L1 Fourier integrals with Hilbert L2 Fourier when
      both the input and actual transform satisfy the true L2 hypotheses.
      Prove genuine normalized spatial/Fourier dilation.
- [x] Prove compact-parameter C1 differentiation from the actual chain
      rule and dominated derivative theorem. Give genuine H1_0 smooth
      approximations for all C1 cube-supported functions, and use these
      results to prove C1/H1_0 membership and the true integral derivative
      formula for each positive Bogovskii truncation.
- [x] Identify the actual normalized spatial mixture and its directional
      derivative's Fourier integral with the checked expression. Prove
      genuine compact Fourier Fubini, actual cube support/continuity and
      both spatial lower/upper-half L2 bounds. Differentiate the genuine
      scalar compact-parameter integral and prove the full scalar derivative
      estimate uniform in positive truncations. Exact Euclidean cube/volume
      transport and actual smooth pressure/moment energy bounds are proved.
- [x] Connect the actual moment-kernel split to all nine physical vector
      derivatives, giving the complete truncation-independent H1 bound.
      The chosen elementary route is Durán, arXiv:1103.3718, Section 2;
      its analytic estimates are checked rather than imported.
- [x] Derive the actual truncated divergence identity by the fundamental
      theorem of calculus along mixtures, prove its zero-mean cancellation
      and pressure limit, and pass from bounded actual approximations to
      genuine Hilbert divergence surjectivity. Density or boundedness alone
      is not a surjectivity proof.
- [x] Prove genuine L2 convergence of the actual mass mixtures with explicit
      positive truncations, a nonsingular pressure formula and dominated
      convergence. Identify the actual Hilbert divergence-error norm with
      the genuine pressure error integral.
- [x] Prove density of actual smooth mean-zero cube pressures using explicit
      normalized mean-corrected tests, the smooth-test fundamental lemma,
      the cube boundary's zero volume and Hilbert orthogonal projection.
- [x] Construct actual uniformly bounded Hilbert Bogovskii truncations.
      Use density and true divergence convergence to obtain uniform
      half-error approximate preimages; prove the complete-space geometric
      series theorem and conclude actual cube-divergence surjectivity.
- [x] Prove a genuine continuous divergence right inverse
      with the precise H1_0 and L2 hypotheses used by the paper.
- [x] Assemble the uniformly bounded divergence right inverse for `k=4,5`,
      treating all `N ≥ 1` and verifying the `N`-independent constant.
- [x] Prove the full actual H1-energy right-inverse variants and genuine
      uniform reduced inf-sup witnesses, including positive denominator
      and nonzero velocity for every nonzero pressure.

The discrete target is defined as `FreudenthalMesh.HasUniformRightInverse`.
`MainTheorem` proves it for both requested degrees without any remaining
mathematical hypothesis. The constant precedes all positive mesh sizes,
and a fixed linear map on each mesh precedes every pressure input. All
energies and derivatives are genuine physical quantities. No project
axiom, placeholder proof or unchecked external oracle is used. The audit
checks the final targets and every project declaration transitively.
