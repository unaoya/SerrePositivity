module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.PathCutLeftEndpoint
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.TwoSidedHomRightEndpoint

/-!
概要：混合 coherent 単体の左端を、反対 nerve の右 Hom 区間の反転で表示する。
方針：対象を反転したラベルで正規化し、Hom では反転 path の最大座標を使う。
規約：元の左射影の係数単体と実際の反対の逆操作を保持する。
使われ方：補間の左端と coherentLeftHomInterval の厳密な照合。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories


/-- 元の左係数の右 Hom の区間単体を反対 nerve から戻した左端の模型。 -/
def coherentTwoSidedHomLeftModel {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {X Y : C} {n : ℕ} (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision (SimplicialCategory.sHom X Y)) _⦋n⦌)
    (t : Fin (n + 1) →o Fin 2) : (SimplicialNerve C) _⦋n⦌ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentOppositeInverseSimplex ((SimplicialNerve Cᵒᵖ).map
    (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableReverseOrderHom t))).op
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonSimplex (X := Opposite.op Y) (Y := Opposite.op X)
      (SSet.opObjEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft _).app _ σ))))

/-- 左端模型の各対象は、反転した切断における元の右 Hom 比較の対象。 -/
lemma coherentTwoSidedHomLeftModel_obj {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {X Y : C} {n : ℕ} (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision (SimplicialCategory.sHom X Y)) _⦋n⦌)
    (t : Fin (n + 1) →o Fin 2) (i : Fin (n + 1)) :
    (coherentTwoSidedHomLeftModel σ t).obj ⟨ULift.up i⟩ =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj (Opposite.op Y) (Opposite.op X)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableReverseOrderHom t) i.rev)).unop := rfl

/-- 零ラベルでの左端模型の対象は元の始域。 -/
lemma coherentTwoSidedHomLeftModel_obj_zero {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} {n : ℕ}
    (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision (SimplicialCategory.sHom X Y)) _⦋n⦌)
    (t : Fin (n + 1) →o Fin 2) (i : Fin (n + 1)) (hi : t i = 0) :
    (coherentTwoSidedHomLeftModel σ t).obj ⟨ULift.up i⟩ = X := by
  rw [coherentTwoSidedHomLeftModel_obj, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut_one _ _ (by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutReverseLabel_one t hi]; decide), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_last]

/-- 一ラベルでの左端模型の対象は元の標的。 -/
lemma coherentTwoSidedHomLeftModel_obj_one {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} {n : ℕ}
    (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision (SimplicialCategory.sHom X Y)) _⦋n⦌)
    (t : Fin (n + 1) →o Fin 2) (i : Fin (n + 1)) (hi : t i ≠ 0) :
    (coherentTwoSidedHomLeftModel σ t).obj ⟨ULift.up i⟩ = Y := by
  rw [coherentTwoSidedHomLeftModel_obj, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut_zero _ _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutReverseLabel_zero t (show t i = 1 by omega)), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_cast]

/-- 補間の左端の coherent 単体は、元の左係数の右区間を反対から戻した模型そのもの。 -/
lemma coherentTwoSidedHomSimplex_zero_model {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} {n : ℕ}
    (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision (SimplicialCategory.sHom X Y)) _⦋n⦌)
    (t : Fin (n + 1) →o Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTwoSidedHomSimplex σ t (OrderHom.const _ 0) = coherentTwoSidedHomLeftModel σ t := by
  apply EnrichedFunctor.ext SSet
    (F := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTwoSidedHomSimplex σ t (OrderHom.const _ 0))
    (G := coherentTwoSidedHomLeftModel σ t) (fun a => by
      by_cases ha : t a.as.down = 0
      · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTwoSidedHomObj_zero X Y t _ ha).trans
          (coherentTwoSidedHomLeftModel_obj_zero σ t _ ha).symm
      · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTwoSidedHomObj_one X Y t _ ha).trans
          (coherentTwoSidedHomLeftModel_obj_one σ t _ ha).symm)
  rintro ⟨⟨i⟩⟩ ⟨⟨j⟩⟩
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTwoSidedHom σ t (OrderHom.const _ 0) i j ≫ eqToHom _ =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentOppositeInverseSimplex _).map ⟨ULift.up i⟩ ⟨ULift.up j⟩
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentOppositeInverseSimplex_map_reverse]
  let a := SSet.opObjEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft (SimplicialCategory.sHom X Y)).app _ σ)
  let r := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableReverseOrderHom t
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTwoSidedHom σ t (OrderHom.const _ 0) i j ≫ eqToHom _ =
    nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutReverseFunctor i j) ≫
      (SimplicialThickening.functor (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut r).uliftMap).map _ _ ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonHom (X := Opposite.op Y) (Y := Opposite.op X) a
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut r j.rev) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut r i.rev)
  by_cases hi : t i = 0 <;> by_cases hj : t j = 0
  · let hA := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_last (Opposite.op Y) (Opposite.op X) n
    let hi' := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut_one r i.rev (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutReverseLabel_one t hi]; decide)
    let hj' := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut_one r j.rev (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutReverseLabel_one t hj]; decide)
    apply (cancel_mono (eqToHom (congrArg₂ SimplicialCategory.sHom
      (congrArg Opposite.unop ((congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj _ _) hi').trans hA))
      (congrArg Opposite.unop ((congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj _ _) hj').trans hA))))).1
    simp only [Category.assoc, eqToHom_trans]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTwoSidedHom_zero_zero σ t (OrderHom.const _ 0) i j hi hj,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparisonHom_transport (X := Opposite.op Y) (Y := Opposite.op X) a hj' hi' hA hA,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparisonHom_last_last]
    apply SSet.hom_ext
    intro d
    rfl
  · let hA := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_cast (Opposite.op Y) (Opposite.op X) j.rev
    let hB := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_last (Opposite.op Y) (Opposite.op X) n
    let hi' := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut_one r i.rev (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutReverseLabel_one t hi]; decide)
    let hj' := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut_zero r j.rev
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutReverseLabel_zero t (show t j = 1 by omega))
    apply (cancel_mono (eqToHom (congrArg₂ SimplicialCategory.sHom
      (congrArg Opposite.unop ((congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj _ _) hi').trans hB))
      (congrArg Opposite.unop ((congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj _ _) hj').trans hA))))).1
    simp only [Category.assoc, eqToHom_trans]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTwoSidedHom_zero_one σ t (OrderHom.const _ 0) i j hi hj,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparisonHom_transport (X := Opposite.op Y) (Y := Opposite.op X) a hj' hi' hA hB,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparisonHom_cast_last, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutEdgewiseStageMap_zero]
    have h := congrArg (fun f => nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutReverseFunctor i j) ≫ f ≫
      SSet.yonedaEquiv.symm a) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut_maximumMap r j.rev i.rev
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutReverseLabel_zero t (show t j = 1 by omega))
        (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutReverseLabel_one t hi]; decide))
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutFirstOneReverseMap, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZeroMap_front]
    dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.thickeningDirectHom]
    simp only [Category.assoc] at h ⊢
    convert h using 1
  · apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro P
    exact False.elim (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutSameSimplex_backward_false t hi hj (P.obj 0))
  · let hAi := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_cast (Opposite.op Y) (Opposite.op X) i.rev
    let hAj := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_cast (Opposite.op Y) (Opposite.op X) j.rev
    let hi' := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut_zero r i.rev
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutReverseLabel_zero t (show t i = 1 by omega))
    let hj' := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut_zero r j.rev
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutReverseLabel_zero t (show t j = 1 by omega))
    apply (cancel_mono (eqToHom (congrArg₂ SimplicialCategory.sHom
      (congrArg Opposite.unop ((congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj _ _) hi').trans hAi))
      (congrArg Opposite.unop ((congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj _ _) hj').trans hAj))))).1
    simp only [Category.assoc, eqToHom_trans]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTwoSidedHom_one_one σ t (OrderHom.const _ 0) i j hi hj,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparisonHom_transport (X := Opposite.op Y) (Y := Opposite.op X) a
        hj' hi' hAj hAi,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparisonHom_cast_cast]
    apply SSet.hom_ext
    intro d
    rfl

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
