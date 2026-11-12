module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.LeftScaffoldComparison

/-!
概要：通常の nerve 上の left scaffold の比較は任意の単体集合への底変換で前合成同値。
方針：有限鎖上の比較を標準単体に移し、底のセル分解で任意の底へ拡張する。
規約：新しい底が nerve や quasicategory であることは要求しない。
使われ方：内ホーンなどへの引き戻しで strict transport の模型と実際の全空間を比較する。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：left scaffold の比較は任意の底変換後も前合成同値となる。
方針：標準単体を有限鎖の nerve と同定し、pullback の自然な比較のセル判定を使う。
規約：底変換の始域は任意の単体集合。
使われ方：Kerodon §5.3.6（Tag 037W）、内ホーンの逆像を strict な模型へ移す。 -/
lemma IsLeftScaffold.overPullback_isPrecompositionEquivalence
    {C : Type u} [Category.{u} C] {E D : SSet.{u}}
    (p : E ⟶ nerve C) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
    (F : C ⥤ SSet.{u}) [∀ c, KanComplex (F.obj c)]
    (l : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement F ⟶ E) (hs : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.IsLeftScaffold p F l)
    (h : l ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F) (g : D ⟶ nerve C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackMap (Over.homMk (U := Over.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F))
        (V := Over.mk p) l h) (Over.mk g)) := by
  let f : Over.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F) ⟶ Over.mk p := Over.homMk l h
  have hstd : ∀ (n : ℕ) (a : (Δ[n] : SSet.{u}) ⟶ nerve C),
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackMap f (Over.mk a)) := by
    intro n a
    let k : nerveFunctor.obj (Cat.of (ULift.{u} (Fin (n + 1)))) ⟶
        nerveFunctor.obj (Cat.of C) := (stdSimplex.isoNerve n).inv ≫ a
    let H := (nerveFunctor.preimage k).toFunctor
    have hH : nerveMap H = (stdSimplex.isoNerve n).inv ≫ a :=
      nerveFunctor.map_preimage _
    let e : Over.mk a ≅ Over.mk (nerveMap H) :=
      Over.isoMk (stdSimplex.isoNerve n) (by
        change (stdSimplex.isoNerve n).hom ≫ nerveMap H = a
        rw [hH, Iso.hom_inv_id_assoc])
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.isPrecompositionEquivalence_over_natComponent_of_iso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackMapNat f) e
      (hs.overPullback_finiteComparison p F l h n H)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.isPrecompositionEquivalence_over_natComponent_of_stdSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackMapNat f)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.isPrecompositionEquivalence_overPullbackMap_initial f) hstd D g

/-- 概要：universal scaffold の比較は内ホーンを含む任意の単体集合への底変換で前合成同値。
方針：strict transport の各係数が Kan であることと scaffold の比較を使う。
規約：底は通常の圏の nerve、底変換は任意。
使われ方：Kerodon §5.3.6（Tag 037W）、全空間の逆像の同値性の strict な模型への還元。 -/
lemma universalScaffold_overPullback_isPrecompositionEquivalence
    {C : Type u} [Category.{u} C] {E D : SSet.{u}}
    (p : E ⟶ nerve C) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (g : D ⟶ nerve C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackMap
      (Over.homMk (U := Over.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram p)))
        (V := Over.mk p) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.universalScaffold p) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.universalScaffold_projection p)) (Over.mk g)) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.universalScaffold_isLeftScaffold p).overPullback_isPrecompositionEquivalence p
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram p) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.universalScaffold p) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.universalScaffold_projection p) g

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
