module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.GradedExtension
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaSphereClosureRetract
public import SerrePositivity.DifferentialGraded.Derived.Basic

public import SerrePositivity.DifferentialGraded.Module.Hom.HomotopyAndOperations
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits Pretriangulated DifferentialGraded HomologicalComplex CochainComplex
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

lemma dgKappaSphereCoversImage_gradedExtension {κ : Cardinal.{u}}
    (hκ : Cardinal.aleph0 < κ) (hreg : κ.IsRegular)
    {M N P : ModuleCategory R D} {f : M ⟶ N} {g : N ⟶ P}
    (s : ModuleGradedSplit R D f g)
    (hM : moduleHomotopicallyProjective R D M) (hP : moduleHomotopicallyProjective R D P)
    (hMI : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereCoversImage R D κ ((moduleToHomotopy R D).obj M))
    (hPI : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereCoversImage R D κ ((moduleToHomotopy R D).obj P)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereCoversImage R D κ ((moduleToHomotopy R D).obj N) := by
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereCoversImage_isTriangulated R D κ hκ hreg
  let q := moduleConeDesc R D f g s.inclusion_projection
  have hi := moduleHomotopicallyProjective_quasiIso_isIso_homotopy R D
    (moduleHomotopicallyProjective_cone R D hM (s.homotopicallyProjective R D hM hP) f)
    hP q (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaGradedSplitConeDesc_quasiIso R D s)
  have hC : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereCoversImage R D κ ((moduleToHomotopy R D).obj (moduleCone R D f)) :=
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereCoversImage R D κ).prop_of_iso (asIso ((moduleToHomotopy R D).map q)).symm hPI
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereCoversImage R D κ).ext_of_isTriangulatedClosed₂
    (moduleHomotopyConeTriangle R D f) (moduleHomotopyConeTriangle_distinguished R D f) hMI hC

end SerrePositivity.InfinityCategories.Project.DerivedCategories
