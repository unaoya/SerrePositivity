module

public import SerrePositivity.InfinityCategories.F1B.KanExtension.LocalShapeOppositeHomotopy
public import SerrePositivity.InfinityCategories.F1B.KanExtension.PointSliceOppositeUncurry

/-!
概要：標準の左 Kan 比較余錐の反転を右 Kan 比較錐と同定する。
方針：局所添字の反転同型と普遍錐の展開の反転を合成する。
規約：頂点の零単体の反転同型も明示する。
使われ方：指定変換に沿う局所輸送を左右で双対化する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：左 Kan の標準余錐の反転は局所添字を戻した右 Kan の標準錐。
方針：coslice の普遍錐を局所添字の反転比較へ制限し、slice の展開の反転を使う。
規約：両辺は同じ join を始域に持つ raw な射。
使われ方：反転した局所輸送の始端の同定。 -/
lemma kanLeftKanCanonicalCocone_op_val {K C D : SSet.{u}}
    (δ : K ⟶ C) (F : C ⟶ D) (c : C _⦋0⦌) :
    joinMap (𝟙 (Δ[0] : SSet.{u})) (kanLeftKanShapeOpIso δ c).hom ≫
      (rightKanCanonicalCone (SSet.opFunctor.map δ) (SSet.opFunctor.map F)
        (SSet.opObjEquiv.symm c)).val =
      joinMap (stdSimplex.opIso ⦋0⦌).inv (𝟙 (leftKanShape δ c).op) ≫
        (stableJoinReverseIso (leftKanShape δ c) Δ[0]).inv ≫
          SSet.opFunctor.map (leftKanCanonicalCocone δ F c).val := by
  dsimp only [rightKanCanonicalCone, leftKanCanonicalCocone]
  rw [← Category.assoc, ← sliceUnderUncurry_precomp, kanLeftKanShapeOpIso_slice,
    kanPointSliceOverOpIso_uncurry, CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]

/-- 概要：左の局所余錐の始域の反転は右の局所錐の始域と同型。
方針：join の反転、標準零単体の反転、局所添字の反転を合わせる。
規約：全て厳密な単体集合の同型。
使われ方：輸送の族の反転で始域を正規化する。 -/
def kanLocalConeOppositeIso {K C : SSet.{u}} (δ : K ⟶ C) (c : C _⦋0⦌) :
    (join (leftKanShape δ c) (Δ[0] : SSet.{u})).op ≅
      join (Δ[0] : SSet.{u})
        (rightKanShape (SSet.opFunctor.map δ) (SSet.opObjEquiv.symm c)) :=
  stableJoinReverseIso (leftKanShape δ c) Δ[0] ≪≫
    joinIso (stdSimplex.opIso ⦋0⦌) (kanLeftKanShapeOpIso δ c)

/-- 概要：正規化した反転同型の左端は元の余錐の頂点の反転。
方針：join の同型の左端と逆反転の境界を計算する。
規約：零単体の反転同型を明示する。
使われ方：輸送の反転の頂点固定条件。 -/
lemma kanLocalConeOppositeIso_inl {K C : SSet.{u}} (δ : K ⟶ C) (c : C _⦋0⦌) :
    joinInl (Δ[0] : SSet.{u})
      (rightKanShape (SSet.opFunctor.map δ) (SSet.opObjEquiv.symm c)) ≫
        (kanLocalConeOppositeIso δ c).inv =
      (stdSimplex.opIso ⦋0⦌).inv ≫
        SSet.opFunctor.map (joinInr (leftKanShape δ c) (Δ[0] : SSet.{u})) := by
  dsimp only [kanLocalConeOppositeIso, Iso.trans_inv, joinIso]
  rw [← Category.assoc, joinInl_joinMap, Category.assoc, stableJoinReverse_inl_inv]

/-- 概要：正規化した反転同型の右端は元の余錐の図式の反転。
方針：join の同型の右端と逆反転の境界を計算する。
規約：局所添字は標準の反転同型の逆で戻す。
使われ方：輸送の反転の図式の条件。 -/
lemma kanLocalConeOppositeIso_inr {K C : SSet.{u}} (δ : K ⟶ C) (c : C _⦋0⦌) :
    joinInr (Δ[0] : SSet.{u})
      (rightKanShape (SSet.opFunctor.map δ) (SSet.opObjEquiv.symm c)) ≫
        (kanLocalConeOppositeIso δ c).inv =
      (kanLeftKanShapeOpIso δ c).inv ≫
        SSet.opFunctor.map (joinInl (leftKanShape δ c) (Δ[0] : SSet.{u})) := by
  dsimp only [kanLocalConeOppositeIso, Iso.trans_inv, joinIso]
  rw [← Category.assoc, joinInr_joinMap, Category.assoc, stableJoinReverse_inr_inv]

/-- 概要：余錐の反転を標準右錐の始域へ正規化すると標準右比較錐に等しい。
方針：局所添字の同型による前合成を消去する。
規約：図式も錐も自然同型ではなく射の等式で比較する。
使われ方：反転した輸送の標準始端。 -/
lemma kanLocalConeOppositeIso_canonical {K C D : SSet.{u}}
    (δ : K ⟶ C) (F : C ⟶ D) (c : C _⦋0⦌) :
    (kanLocalConeOppositeIso δ c).inv ≫
      SSet.opFunctor.map (leftKanCanonicalCocone δ F c).val =
        (rightKanCanonicalCone (SSet.opFunctor.map δ) (SSet.opFunctor.map F)
          (SSet.opObjEquiv.symm c)).val := by
  apply (cancel_epi (joinMap (𝟙 (Δ[0] : SSet.{u}))
    (kanLeftKanShapeOpIso δ c).hom)).1
  rw [← Category.assoc]
  have h : joinMap (𝟙 (Δ[0] : SSet.{u})) (kanLeftKanShapeOpIso δ c).hom ≫
      (kanLocalConeOppositeIso δ c).inv =
        joinMap (stdSimplex.opIso ⦋0⦌).inv (𝟙 (leftKanShape δ c).op) ≫
          (stableJoinReverseIso (leftKanShape δ c) Δ[0]).inv := by
    dsimp only [kanLocalConeOppositeIso, Iso.trans_inv, joinIso]
    rw [← Category.assoc, ← joinMap_comp, Category.id_comp, Iso.hom_inv_id]
  rw [h, Category.assoc, kanLeftKanCanonicalCocone_op_val]

end SerrePositivity.InfinityCategories.F1B
