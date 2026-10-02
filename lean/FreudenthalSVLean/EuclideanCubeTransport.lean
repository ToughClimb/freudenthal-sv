import FreudenthalSVLean.CubeSupportedMixtures
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Actual cube and compact-parameter volume transport

For the continuous lifting in manuscript Lemma `means`, the fixed
coordinate homeomorphism transports genuine cube-restricted Lebesgue
integrals exactly. Its product with the time identity likewise transports
the actual compact time/cube integrals, with no implicit norm or volume
identification. The affine mixture argument becomes the actual physical
Bogovskii kernel argument by an explicit linear-coordinate identity.
-/

open MeasureTheory Set
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.EuclideanCoordinateTransport
open FreudenthalSVLean.CubeSupportedMixtures
open FreudenthalSVLean.BogovskiiCubeGeometry

noncomputable section

namespace FreudenthalSVLean.EuclideanCubeTransport

set_option backward.isDefEq.respectTransparency false

abbrev E := EuclideanThree

theorem integral_cube_pullback {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Space → F) : (∫ x in cubeE, f (coordinates x)) = ∫ x in cube, f x :=
  (coordinates_volume.restrict_preimage (show MeasurableSet cube from measurableSet_Icc)).integral_comp
    (MeasurableEquiv.toLp 2 Space).symm.measurableEmbedding f

theorem integral_parameter_pullback {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ε : ℝ} (f : ℝ × Space → F) (hf : Continuous f) :
    (∫ p in Icc ε (1 : ℝ) ×ˢ cubeE, f (p.1, coordinates p.2)) =
      ∫ p in Icc ε (1 : ℝ) ×ˢ cube, f p := by
  have hp : Continuous (fun p : ℝ × E => f (p.1, coordinates p.2)) :=
    hf.comp (continuous_fst.prodMk (coordinates.continuous.comp continuous_snd))
  have hi : IntegrableOn (fun p : ℝ × E => f (p.1, coordinates p.2))
      (Icc ε (1 : ℝ) ×ˢ cubeE) :=
    hp.continuousOn.integrableOn_compact (isCompact_Icc.prod cubeE_compact)
  have hj : IntegrableOn f (Icc ε (1 : ℝ) ×ˢ cube) :=
    hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have he : (volume : Measure (ℝ × E)).restrict (Icc ε (1 : ℝ) ×ˢ cubeE) =
      (volume.restrict (Icc ε (1 : ℝ))).prod ((volume : Measure E).restrict cubeE) :=
    (Measure.prod_restrict (Icc ε (1 : ℝ)) cubeE).symm
  have he' : (volume : Measure (ℝ × Space)).restrict (Icc ε (1 : ℝ) ×ˢ cube) =
      (volume.restrict (Icc ε (1 : ℝ))).prod ((volume : Measure Space).restrict cube) :=
    (Measure.prod_restrict (Icc ε (1 : ℝ)) cube).symm
  change Integrable _ (volume.restrict (Icc ε (1 : ℝ) ×ˢ cubeE)) at hi
  change Integrable _ (volume.restrict (Icc ε (1 : ℝ) ×ˢ cube)) at hj
  rw [he] at hi ⊢
  rw [he'] at hj ⊢
  rw [integral_prod _ hi, integral_prod _ hj]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t => integral_cube_pullback (fun y => f (t, y)))

theorem coordinates_mixtureArgument {t : ℝ} (ht : t ≠ 0) (x y : E) :
    coordinates (mixtureArgument t x y) = kernelArgument t (coordinates x) (coordinates y) := by
  funext i
  change t⁻¹ * (x i - (1 - t) * y i) = y i + t⁻¹ * (x i - y i)
  field_simp
  ring

end FreudenthalSVLean.EuclideanCubeTransport
