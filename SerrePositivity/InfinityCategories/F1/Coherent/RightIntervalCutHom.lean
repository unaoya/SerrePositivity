module

public import SerrePositivity.InfinityCategories.F1.Coherent.RightIntervalCutSimplex

/-!
概要：元の右区間の非定値な Hom 作用を、同じ path と元の Hom 単体で表示する。
方針：切断の二端点を正規化し、既存の coherent Hom 比較の最後への作用を使う。
規約：単体的圏は任意で、局所 Kan 性は不要。
使われ方：分類作用の第一三角形の非定値 Hom を成分 fiber の等式へ接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 元の右区間の混合 Hom は、同じ切断の path の後の最大元評価と元の Hom 単体。 -/
lemma coherentRightIntervalCutSimplex_mixedHom
    {C : Type v} [Category.{u} C] [SimplicialCategory C] {X Y : C} {n : ℕ}
    (s : (SimplicialCategory.sHom X Y) _⦋n⦌) (t : Fin (n + 1) →o Fin 2)
    (i j : Fin (n + 1)) (hi : t i = 0) (hj : t j = 1) :
    (coherentRightIntervalCutSimplex s t).map ⟨ULift.up i⟩ ⟨ULift.up j⟩ ≫
        eqToHom (congrArg₂ SimplicialCategory.sHom
          (coherentRightIntervalCutSimplex_obj_zero s t i hi)
          (coherentRightIntervalCutSimplex_obj_one s t j hj)) =
      ((SimplicialThickening.functor (coherentPrismCut t).uliftMap).map
          (⟨ULift.up i⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1)))) ⟨ULift.up j⟩ ≫
        eqToHom (congrArg₂ (fun a b : Fin (n + 2) ↦ SimplicialCategory.sHom
          (⟨ULift.up a⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2)))) ⟨ULift.up b⟩)
          (coherentPrismCut_zero t i hi)
          (coherentPrismCut_one t j (by rw [hj]; decide)))) ≫
        pathLastMaximumMap i ≫ SSet.yonedaEquiv.symm s := by
  change (_ ≫ coherentHomComparisonHom s (coherentPrismCut t i)
    (coherentPrismCut t j)) ≫ eqToHom _ = _
  rw [Category.assoc, coherentHomComparisonHom_transport s
    (coherentPrismCut_zero t i hi) (coherentPrismCut_one t j (by rw [hj]; decide))
    (coherentHomComparisonObj_cast X Y i) (coherentHomComparisonObj_last X Y n),
    coherentHomComparisonHom_cast_last]
  simp only [Category.assoc]
  rfl

/-- 同時刻零の Hom 作用は、始域の豊穣恒等に全 path で定値。 -/
lemma coherentRightIntervalCutSimplex_zeroHom
    {C : Type v} [Category.{u} C] [SimplicialCategory C] {X Y : C} {n : ℕ}
    (s : (SimplicialCategory.sHom X Y) _⦋n⦌) (t : Fin (n + 1) →o Fin 2)
    (i j : Fin (n + 1)) (hi : t i = 0) (hj : t j = 0) :
    (coherentRightIntervalCutSimplex s t).map ⟨ULift.up i⟩ ⟨ULift.up j⟩ ≫
        eqToHom (congrArg₂ SimplicialCategory.sHom
          (coherentRightIntervalCutSimplex_obj_zero s t i hi)
          (coherentRightIntervalCutSimplex_obj_zero s t j hj)) = toUnit _ ≫ eId SSet X := by
  change (_ ≫ coherentHomComparisonHom s (coherentPrismCut t i)
    (coherentPrismCut t j)) ≫ eqToHom _ = _
  rw [Category.assoc, coherentHomComparisonHom_transport s
    (coherentPrismCut_zero t i hi) (coherentPrismCut_zero t j hj)
    (coherentHomComparisonObj_cast X Y i) (coherentHomComparisonObj_cast X Y j),
    coherentHomComparisonHom_cast_cast]
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro P
  rfl

/-- 同時刻一の Hom 作用は、終域の豊穣恒等に全 path で定値。 -/
lemma coherentRightIntervalCutSimplex_oneHom
    {C : Type v} [Category.{u} C] [SimplicialCategory C] {X Y : C} {n : ℕ}
    (s : (SimplicialCategory.sHom X Y) _⦋n⦌) (t : Fin (n + 1) →o Fin 2)
    (i j : Fin (n + 1)) (hi : t i = 1) (hj : t j = 1) :
    (coherentRightIntervalCutSimplex s t).map ⟨ULift.up i⟩ ⟨ULift.up j⟩ ≫
        eqToHom (congrArg₂ SimplicialCategory.sHom
          (coherentRightIntervalCutSimplex_obj_one s t i hi)
          (coherentRightIntervalCutSimplex_obj_one s t j hj)) = toUnit _ ≫ eId SSet Y := by
  change (_ ≫ coherentHomComparisonHom s (coherentPrismCut t i)
    (coherentPrismCut t j)) ≫ eqToHom _ = _
  rw [Category.assoc, coherentHomComparisonHom_transport s
    (coherentPrismCut_one t i (by rw [hi]; decide))
    (coherentPrismCut_one t j (by rw [hj]; decide))
    (coherentHomComparisonObj_last X Y n) (coherentHomComparisonObj_last X Y n),
    coherentHomComparisonHom_last_last]
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro P
  rfl

end SerrePositivity.InfinityCategories
