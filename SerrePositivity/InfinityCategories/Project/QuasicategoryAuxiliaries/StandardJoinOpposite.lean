module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinReverse
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinTensorPoint

/-! # 辺と点の join の標準表示と反転

概要：点と辺の join を反転すると、辺と点の join の標準表示になる。
方針：標準二単体の三頂点における写像を比較する。
規約：反転によって二因子の順序を交換する。
使われ方：標準 cospan の錐と標準 span の余錐の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries

/-- 概要：点と辺の標準 join の反転は辺と点の標準 join と両立する。
方針：反転した二単体を通常の二単体へ戻して Yoneda で計算する。
規約：順方向の join 反転を用いる。使われ方：四角形の二三角形の比較。 -/
lemma stableJoinReverse_stdSimplex_zero_one :
    SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso.{u} 0 1).inv ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinReverseIso Δ[0] Δ[1]).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.opIso ⦋1⦌).hom (stdSimplex.opIso ⦋0⦌).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 1 0).hom = (stdSimplex.opIso ⦋2⦌).hom := by
  apply (cancel_epi (stdSimplex.opIso ⦋2⦌).inv).1
  apply SSet.yonedaEquiv.injective
  apply stdSimplex.ext
  intro i
  fin_cases i <;> rfl

/-- 概要：辺と点から元の反転した点と辺へ戻す標準表示の式。
方針：順方向の同型の等式の逆射を取り、標準表示の同型を消去する。
規約：標準二単体への射として書く。使われ方：反転四角形の三角形の計算。 -/
lemma stableJoinReverse_stdSimplex_zero_one_inv :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.opIso ⦋1⦌).inv (stdSimplex.opIso ⦋0⦌).inv ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinReverseIso Δ[0] Δ[1]).inv ≫
      SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso.{u} 0 1).hom =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 1 0).hom ≫ (stdSimplex.opIso ⦋2⦌).inv := by
  let e := (SSet.opFunctor.mapIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso.{u} 0 1).symm) ≪≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinReverseIso Δ[0] Δ[1] ≪≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinIso (stdSimplex.opIso ⦋1⦌) (stdSimplex.opIso ⦋0⦌) ≪≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 1 0
  have he : e = stdSimplex.opIso ⦋2⦌ := Iso.ext stableJoinReverse_stdSimplex_zero_one
  have h := congrArg (fun e ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso.{u} 1 0).hom ≫ e.inv) he
  dsimp [e, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinIso] at h
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using h

/-- 概要：標準三角形からの join 反転は標準単体の反転に等しい。
方針：直前の式の両側から標準表示の同型を消去する。
規約：始域は通常の二単体。使われ方：span の二三角形の反転。 -/
lemma stableJoinReverse_stdSimplex_zero_one_inv_triangle :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso.{u} 1 0).inv ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.opIso ⦋1⦌).inv (stdSimplex.opIso ⦋0⦌).inv ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinReverseIso Δ[0] Δ[1]).inv =
        (stdSimplex.opIso ⦋2⦌).inv ≫ SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 1).inv := by
  apply (cancel_mono (SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 1).hom)).1
  simp only [Category.assoc, stableJoinReverse_stdSimplex_zero_one_inv,
    Iso.inv_hom_id_assoc, ← CategoryTheory.Functor.map_comp,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.comp_id]

end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
