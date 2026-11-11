module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleOutputUnliftedPrecomp
/-!
概要：同じ共通対象宇宙への入力持ち上げは、二段の dg 前合成を厳密に保つ。
方針：中間の対象の上げ下げを展開し、元の二つの Hom 鎖写像の合成へ戻す。
規約：対象宇宙以外を変更しない。使われ方：指定出力分解の前合成合成則。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (A B C : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R A] [_root_.SerrePositivity.DifferentialGraded.DGCategory R B] [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
/-- 中間の対象持ち上げの往復を通る二段前合成は、同じ合成入力の持ち上げと一致する。 -/
lemma dgUniverseLift_inputPrecomp_comp (H : _root_.SerrePositivity.DifferentialGraded.DGFunctor R A B) (J : _root_.SerrePositivity.DifferentialGraded.DGFunctor R B C) :
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, v, max (u + 1) w} R A).comp
      (H.comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, v, max (u + 1) w} R B))).comp
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, v, max (u + 1) w} R B).comp
          (J.comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, v, max (u + 1) w} R C))) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, v, max (u + 1) w} R A).comp
        ((H.comp J).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, v, max (u + 1) w} R C)) := by
  apply EnrichedFunctor.ext (_root_.SerrePositivity.DifferentialGraded.Complex R)
    (F := ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, v, max (u + 1) w} R A).comp
      (H.comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, v, max (u + 1) w} R B))).comp
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, v, max (u + 1) w} R B).comp
          (J.comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, v, max (u + 1) w} R C))))
    (G := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, v, max (u + 1) w} R A).comp
      ((H.comp J).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, v, max (u + 1) w} R C))) (fun _ => rfl)
  intro X Y
  simp only [EnrichedFunctor.comp_map, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp,
    _root_.SerrePositivity.InfinityCategories.dgObjectImageEvaluation, eqToHom_refl, Category.comp_id, Category.id_comp]
  rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories
