module
public import SerrePositivity.InfinityCategories.Derived.KappaCovers.HomotopyRetract
public import SerrePositivity.DifferentialGraded.Derived.GradedExtensionProjective
public import SerrePositivity.DifferentialGraded.Derived.ProjectiveFiniteOperations
public import SerrePositivity.DifferentialGraded.Module.ConeDesc
public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact

/-!
概要：実加群の全次数分裂する拡大に沿って、同じ選択代表系による被覆を延長する。
方針：同じ cone 射影の評価別準同型性を示し、射影的二端点で K(D) の同型へ戻す。
規約：分裂の section を閉射として扱わない。使われ方：κ-small semifree の有限層。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits Pretriangulated DifferentialGraded HomologicalComplex CochainComplex
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

set_option maxHeartbeats 800000 in
lemma dgKappaGradedSplitConeDesc_quasiIso {M N P : ModuleCategory R D}
    {f : M ⟶ N} {g : N ⟶ P} (s : ModuleGradedSplit R D f g) :
    moduleQuasiIso R D (moduleConeDesc R D f g s.inclusion_projection) := by
  intro x
  rw [moduleConeDesc_eval]
  let S := (ShortComplex.mk f g s.inclusion_projection).map (moduleEvaluation R D x)
  have hS : S.ShortExact := HomologicalComplex.shortExact_of_degreewise_shortExact S
    (fun n => s.evaluationShortExact x n)
  convert mappingCone.quasiIso_descShortComplex hS using 1 <;> rfl

lemma dgKappaCoversImage_gradedExtension {κ : Cardinal.{u}}
    (hκ : Cardinal.aleph0 < κ) (hreg : κ.IsRegular)
    {M N P : ModuleCategory R D} {f : M ⟶ N} {g : N ⟶ P}
    (s : ModuleGradedSplit R D f g)
    (hM : moduleHomotopicallyProjective R D M) (hP : moduleHomotopicallyProjective R D P)
    (hMI : dgKappaCoversImage R D κ ((moduleToHomotopy R D).obj M))
    (hPI : dgKappaCoversImage R D κ ((moduleToHomotopy R D).obj P)) :
    dgKappaCoversImage R D κ ((moduleToHomotopy R D).obj N) := by
  let := dgKappaCoversImage_isTriangulated R D κ hκ hreg
  let q := moduleConeDesc R D f g s.inclusion_projection
  have hi := moduleHomotopicallyProjective_quasiIso_isIso_homotopy R D
    (moduleHomotopicallyProjective_cone R D hM (s.homotopicallyProjective R D hM hP) f)
    hP q (dgKappaGradedSplitConeDesc_quasiIso R D s)
  have hC : dgKappaCoversImage R D κ ((moduleToHomotopy R D).obj (moduleCone R D f)) :=
    (dgKappaCoversImage R D κ).prop_of_iso (asIso ((moduleToHomotopy R D).map q)).symm hPI
  exact (dgKappaCoversImage R D κ).ext_of_isTriangulatedClosed₂
    (moduleHomotopyConeTriangle R D f) (moduleHomotopyConeTriangle_distinguished R D f) hMI hC

end SerrePositivity.InfinityCategories
