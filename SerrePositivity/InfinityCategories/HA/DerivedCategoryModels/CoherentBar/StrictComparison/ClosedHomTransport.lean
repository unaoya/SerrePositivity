module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeCoordinates
public import SerrePositivity.DifferentialGraded.Module.Hom.ConeComparison

/-!
概要：閉零射の端点等号による移送と、同じ斉次 Hom の移送を照合する。
方針：二つの端点等号を消去する。
規約：等号射による実加群射を保持する。
使われ方：native 余錐の零次元列を同じ閉射へ戻す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]

lemma dgBarClosedHom_transport {M N M' N' : _root_.SerrePositivity.DifferentialGraded.RightModule R D}
    (hx : M = M') (hy : N = N')
    (f : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) M ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) N) :
    (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv R (_root_.SerrePositivity.DifferentialGraded.RightModule R D) _ _
      (eqToHom (congrArg (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R)) hx.symm) ≫ f ≫
        eqToHom (congrArg (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R)) hy))).val =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport hx hy rfl
        (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv R (_root_.SerrePositivity.DifferentialGraded.RightModule R D) _ _ f).val := by
  subst M'
  subst N'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
