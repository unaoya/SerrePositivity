module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PairLeftRepresentability
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.YonedaInfinityFullyFaithful
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorComposition

/-!
概要：元の全右関手圏の反対を共変表現可能関手の圏へ埋め込む。
方針：反対圏の Yoneda と二重反転の厳密な前合成を使う。
規約：元の全関手圏を core に置き換えない。
使われ方：実単位族の表現可能性から反変の随伴関手を回収する。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：元の圏の反対から共変表現可能関手の全圏への実際の Yoneda 写像。
方針：反対圏の Yoneda の後に二重反転の逆同型による前合成を行う。
規約：全自然変換と高次単体に作用する。
使われ方：対ごとの右随伴を表現可能関手から回収する。 -/
def pairCovariantYoneda (B : SSet.{u}) [Quasicategory B] :
    (SSet.uliftFunctor.{u + 1, u}).obj B.op ⟶
      (ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap B.op ≫
    (pre ((SSet.uliftFunctor.{u + 1, u}).map (SSet.opFunctorCompOpFunctorIso.app B).inv)).app
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}

/-- 概要：同じ共変 Yoneda 写像は元の反対圏を充満忠実に埋め込む。
方針：既存の Yoneda の充満忠実性に、同型による前合成の同値性を接続する。
規約：同値の存在や全関手圏の双対性は仮定しない。
使われ方：元の右関手の全高次の回収。 -/
lemma pairCovariantYoneda_isFullyFaithful (B : SSet.{u}) [Quasicategory B] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (pairCovariantYoneda B) := by
  let e : (SSet.uliftFunctor.{u + 1, u}).obj B ≅
      (SSet.uliftFunctor.{u + 1, u}).obj B.op.op :=
    (SSet.uliftFunctor.{u + 1, u}).mapIso (SSet.opFunctorCompOpFunctorIso.app B).symm
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap_isFullyFaithful B.op).comp
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso e).precompose _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}).isQCatEquivalence.isFullyFaithful)

/-- 概要：共変 Yoneda の元の二頂点の同型を実際に回収する。
方針：証明済みの充満忠実性の逆像を、元の二頂点に一度だけ構成する。
規約：実装を保持する不透明な定義であり、公理や存在仮定ではない。
使われ方：複雑な単位族の値での型の正規化を局所化する。 -/
opaque pairCovariantYonedaPreimageVertexIso (B : SSet.{u}) [Quasicategory B]
    {x y : ((SSet.uliftFunctor.{u + 1, u}).obj B.op) _⦋0⦌}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((pairCovariantYoneda B).app (Opposite.op ⦋0⦌) x)
      ((pairCovariantYoneda B).app (Opposite.op ⦋0⦌) y)) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso x y :=
  (pairCovariantYoneda_isFullyFaithful B).preimageVertexIso e

/-- 概要：共変 Yoneda の各頂点は元の共変表現可能関手そのもの。
方針：元の Yoneda の頂点公式を二重反転の前合成に通す。
規約：対象ごとの同型ではなく頂点の厳密な等式。
使われ方：元の右関手の表現可能性との照合。 -/
lemma pairCovariantYoneda_vertex {B : SSet.{u}} [Quasicategory B] (w : B.op _⦋0⦌) :
    (pairCovariantYoneda B).app (Opposite.op ⦋0⦌) (ULift.up w) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.covariantRepresentableInfinity (SSet.opObjEquiv w)) := by
  change ((pre ((SSet.uliftFunctor.{u + 1, u}).map
    (SSet.opFunctorCompOpFunctorIso.app B).inv)).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}).app (Opposite.op ⦋0⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap B.op).app (Opposite.op ⦋0⦌) (ULift.up w)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap_vertex]
  rfl

/-- 概要：元の全単位族の全ての左頂点は共変 Yoneda の本質像に属する。
方針：d で選んだ右随伴が同じ固定左値を表現することを使う。
規約：全左関手族の元の頂点に対する主張。
使われ方：反変の随伴関手の実際の単体写像への持ち上げ。 -/
lemma pairUnitHomFamily_in_covariantYonedaImage (C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u})
    (v : ((SSet.uliftFunctor.{u + 2, u + 1}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLFunctorSpace C D)) _⦋0⦌) :
    ∃ w, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
      ((pairCovariantYoneda (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRFunctorSpace D C)).app (Opposite.op ⦋0⦌) w)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairUnitHomFamily C D).app (Opposite.op ⦋0⦌) v)) := by
  obtain ⟨v⟩ := v
  let w := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightAdjointVertex v
  have a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftVertexFunctor v) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightVertexFunctor w) := by
    simpa only [w, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightAdjointVertex, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightFunctorVertex, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightVertexFunctor,
      Equiv.symm_apply_apply] using _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.chosenRightAdjunction v
  refine ⟨ULift.up (SSet.opObjEquiv.symm w), ?_⟩
  rw [pairCovariantYoneda_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairUnitHomFamily_vertex, Equiv.apply_symm_apply]
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairUnitHomAtLeft_representationIso v w a⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
