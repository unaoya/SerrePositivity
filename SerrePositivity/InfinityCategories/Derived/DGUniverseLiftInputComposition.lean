module
public import SerrePositivity.InfinityCategories.Derived.DGModuleOutputUnliftedPrecomp
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (A B C : Type v)
  [DGCategory R A] [DGCategory R B] [DGCategory R C]
/-- 中間の対象持ち上げの往復を通る二段前合成は、同じ合成入力の持ち上げと一致する。 -/
lemma dgUniverseLift_inputPrecomp_comp (H : DGFunctor R A B) (J : DGFunctor R B C) :
    ((dgUniverseLiftDown.{u, v, max (u + 1) w} R A).comp
      (H.comp (dgUniverseLiftUp.{u, v, max (u + 1) w} R B))).comp
        ((dgUniverseLiftDown.{u, v, max (u + 1) w} R B).comp
          (J.comp (dgUniverseLiftUp.{u, v, max (u + 1) w} R C))) =
      (dgUniverseLiftDown.{u, v, max (u + 1) w} R A).comp
        ((H.comp J).comp (dgUniverseLiftUp.{u, v, max (u + 1) w} R C)) := by
  apply EnrichedFunctor.ext (Complex R)
    (F := ((dgUniverseLiftDown.{u, v, max (u + 1) w} R A).comp
      (H.comp (dgUniverseLiftUp.{u, v, max (u + 1) w} R B))).comp
        ((dgUniverseLiftDown.{u, v, max (u + 1) w} R B).comp
          (J.comp (dgUniverseLiftUp.{u, v, max (u + 1) w} R C))))
    (G := (dgUniverseLiftDown.{u, v, max (u + 1) w} R A).comp
      ((H.comp J).comp (dgUniverseLiftUp.{u, v, max (u + 1) w} R C))) (fun _ => rfl)
  intro X Y
  simp only [EnrichedFunctor.comp_map, dgUniverseLiftDown, dgUniverseLiftUp,
    dgObjectImageEvaluation, eqToHom_refl, Category.comp_id, Category.id_comp]
  rfl
end SerrePositivity.InfinityCategories
