module

public import SerrePositivity.InfinityCategories.F1.CoherentPathCutLeftEndpoint
public import SerrePositivity.InfinityCategories.F1.CoherentTwoSidedHomRightEndpoint

/-!
概要：混合 coherent 単体の左端を、反対 nerve の右 Hom 区間の反転で表示する。
方針：対象を反転したラベルで正規化し、Hom では反転 path の最大座標を使う。
規約：元の左射影の係数単体と実際の反対の逆操作を保持する。
使われ方：補間の左端と coherentLeftHomInterval の厳密な照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
open HomotopyLimits

/-- 元の左係数の右 Hom の区間単体を反対 nerve から戻した左端の模型。 -/
def coherentTwoSidedHomLeftModel {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {X Y : C} {n : ℕ} (σ : (edgewiseSubdivision (SimplicialCategory.sHom X Y)) _⦋n⦌)
    (t : Fin (n + 1) →o Fin 2) : (SimplicialNerve C) _⦋n⦌ :=
  coherentOppositeInverseSimplex ((SimplicialNerve Cᵒᵖ).map
    (SimplexCategory.mkHom (coherentPrismCut (stableReverseOrderHom t))).op
    (coherentHomComparisonSimplex (X := Opposite.op Y) (Y := Opposite.op X)
      (SSet.opObjEquiv ((edgewiseLeft _).app _ σ))))

/-- 左端模型の各対象は、反転した切断における元の右 Hom 比較の対象。 -/
lemma coherentTwoSidedHomLeftModel_obj {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {X Y : C} {n : ℕ} (σ : (edgewiseSubdivision (SimplicialCategory.sHom X Y)) _⦋n⦌)
    (t : Fin (n + 1) →o Fin 2) (i : Fin (n + 1)) :
    (coherentTwoSidedHomLeftModel σ t).obj ⟨ULift.up i⟩ =
    (coherentHomComparisonObj (Opposite.op Y) (Opposite.op X)
      (coherentPrismCut (stableReverseOrderHom t) i.rev)).unop := rfl

/-- 零ラベルでの左端模型の対象は元の始域。 -/
lemma coherentTwoSidedHomLeftModel_obj_zero {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} {n : ℕ}
    (σ : (edgewiseSubdivision (SimplicialCategory.sHom X Y)) _⦋n⦌)
    (t : Fin (n + 1) →o Fin 2) (i : Fin (n + 1)) (hi : t i = 0) :
    (coherentTwoSidedHomLeftModel σ t).obj ⟨ULift.up i⟩ = X := by
  rw [coherentTwoSidedHomLeftModel_obj, coherentPrismCut_one _ _ (by
    rw [pathCutReverseLabel_one t hi]; decide), coherentHomComparisonObj_last]

/-- 一ラベルでの左端模型の対象は元の標的。 -/
lemma coherentTwoSidedHomLeftModel_obj_one {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} {n : ℕ}
    (σ : (edgewiseSubdivision (SimplicialCategory.sHom X Y)) _⦋n⦌)
    (t : Fin (n + 1) →o Fin 2) (i : Fin (n + 1)) (hi : t i ≠ 0) :
    (coherentTwoSidedHomLeftModel σ t).obj ⟨ULift.up i⟩ = Y := by
  rw [coherentTwoSidedHomLeftModel_obj, coherentPrismCut_zero _ _
    (pathCutReverseLabel_zero t (show t i = 1 by omega)), coherentHomComparisonObj_cast]

/-- 補間の左端の coherent 単体は、元の左係数の右区間を反対から戻した模型そのもの。 -/
lemma coherentTwoSidedHomSimplex_zero_model {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} {n : ℕ}
    (σ : (edgewiseSubdivision (SimplicialCategory.sHom X Y)) _⦋n⦌)
    (t : Fin (n + 1) →o Fin 2) :
    coherentTwoSidedHomSimplex σ t (OrderHom.const _ 0) = coherentTwoSidedHomLeftModel σ t := by
  apply EnrichedFunctor.ext SSet
    (F := coherentTwoSidedHomSimplex σ t (OrderHom.const _ 0))
    (G := coherentTwoSidedHomLeftModel σ t) (fun a => by
      by_cases ha : t a.as.down = 0
      · exact (coherentTwoSidedHomObj_zero X Y t _ ha).trans
          (coherentTwoSidedHomLeftModel_obj_zero σ t _ ha).symm
      · exact (coherentTwoSidedHomObj_one X Y t _ ha).trans
          (coherentTwoSidedHomLeftModel_obj_one σ t _ ha).symm)
  rintro ⟨⟨i⟩⟩ ⟨⟨j⟩⟩
  change coherentTwoSidedHom σ t (OrderHom.const _ 0) i j ≫ eqToHom _ =
    (coherentOppositeInverseSimplex _).map ⟨ULift.up i⟩ ⟨ULift.up j⟩
  rw [coherentOppositeInverseSimplex_map_reverse]
  let a := SSet.opObjEquiv ((edgewiseLeft (SimplicialCategory.sHom X Y)).app _ σ)
  let r := stableReverseOrderHom t
  change coherentTwoSidedHom σ t (OrderHom.const _ 0) i j ≫ eqToHom _ =
    nerveMap (pathCutReverseFunctor i j) ≫
      (SimplicialThickening.functor (coherentPrismCut r).uliftMap).map _ _ ≫
        coherentHomComparisonHom (X := Opposite.op Y) (Y := Opposite.op X) a
          (coherentPrismCut r j.rev) (coherentPrismCut r i.rev)
  by_cases hi : t i = 0 <;> by_cases hj : t j = 0
  · let hA := coherentHomComparisonObj_last (Opposite.op Y) (Opposite.op X) n
    let hi' := coherentPrismCut_one r i.rev (by rw [pathCutReverseLabel_one t hi]; decide)
    let hj' := coherentPrismCut_one r j.rev (by rw [pathCutReverseLabel_one t hj]; decide)
    apply (cancel_mono (eqToHom (congrArg₂ SimplicialCategory.sHom
      (congrArg Opposite.unop ((congrArg (coherentHomComparisonObj _ _) hi').trans hA))
      (congrArg Opposite.unop ((congrArg (coherentHomComparisonObj _ _) hj').trans hA))))).1
    simp only [Category.assoc, eqToHom_trans]
    rw [coherentTwoSidedHom_zero_zero σ t (OrderHom.const _ 0) i j hi hj,
      coherentHomComparisonHom_transport (X := Opposite.op Y) (Y := Opposite.op X) a hj' hi' hA hA,
      coherentHomComparisonHom_last_last]
    apply SSet.hom_ext
    intro d
    rfl
  · let hA := coherentHomComparisonObj_cast (Opposite.op Y) (Opposite.op X) j.rev
    let hB := coherentHomComparisonObj_last (Opposite.op Y) (Opposite.op X) n
    let hi' := coherentPrismCut_one r i.rev (by rw [pathCutReverseLabel_one t hi]; decide)
    let hj' := coherentPrismCut_zero r j.rev
      (pathCutReverseLabel_zero t (show t j = 1 by omega))
    apply (cancel_mono (eqToHom (congrArg₂ SimplicialCategory.sHom
      (congrArg Opposite.unop ((congrArg (coherentHomComparisonObj _ _) hi').trans hB))
      (congrArg Opposite.unop ((congrArg (coherentHomComparisonObj _ _) hj').trans hA))))).1
    simp only [Category.assoc, eqToHom_trans]
    rw [coherentTwoSidedHom_zero_one σ t (OrderHom.const _ 0) i j hi hj,
      coherentHomComparisonHom_transport (X := Opposite.op Y) (Y := Opposite.op X) a hj' hi' hA hB,
      coherentHomComparisonHom_cast_last, pathCutEdgewiseStageMap_zero]
    have h := congrArg (fun f => nerveMap (pathCutReverseFunctor i j) ≫ f ≫
      SSet.yonedaEquiv.symm a) (coherentPrismCut_maximumMap r j.rev i.rev
        (pathCutReverseLabel_zero t (show t j = 1 by omega))
        (by rw [pathCutReverseLabel_one t hi]; decide))
    rw [pathCutFirstOneReverseMap, pathCutLastZeroMap_front]
    dsimp only [thickeningDirectHom]
    simp only [Category.assoc] at h ⊢
    convert h using 1
  · apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro P
    exact False.elim (pathCutSameSimplex_backward_false t hi hj (P.obj 0))
  · let hAi := coherentHomComparisonObj_cast (Opposite.op Y) (Opposite.op X) i.rev
    let hAj := coherentHomComparisonObj_cast (Opposite.op Y) (Opposite.op X) j.rev
    let hi' := coherentPrismCut_zero r i.rev
      (pathCutReverseLabel_zero t (show t i = 1 by omega))
    let hj' := coherentPrismCut_zero r j.rev
      (pathCutReverseLabel_zero t (show t j = 1 by omega))
    apply (cancel_mono (eqToHom (congrArg₂ SimplicialCategory.sHom
      (congrArg Opposite.unop ((congrArg (coherentHomComparisonObj _ _) hi').trans hAi))
      (congrArg Opposite.unop ((congrArg (coherentHomComparisonObj _ _) hj').trans hAj))))).1
    simp only [Category.assoc, eqToHom_trans]
    rw [coherentTwoSidedHom_one_one σ t (OrderHom.const _ 0) i j hi hj,
      coherentHomComparisonHom_transport (X := Opposite.op Y) (Y := Opposite.op X) a
        hj' hi' hAj hAi,
      coherentHomComparisonHom_cast_cast]
    apply SSet.hom_ext
    intro d
    rfl

end SerrePositivity.InfinityCategories
