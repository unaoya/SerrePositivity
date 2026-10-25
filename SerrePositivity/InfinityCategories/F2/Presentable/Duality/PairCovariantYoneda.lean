module

public import SerrePositivity.InfinityCategories.F2.Presentable.Duality.PairLeftRepresentability
public import SerrePositivity.InfinityCategories.F1.Yoneda.YonedaInfinityFullyFaithful
public import SerrePositivity.InfinityCategories.Core.FunctorComposition

/-!
概要：元の全右関手圏の反対を共変表現可能関手の圏へ埋め込む。
方針：反対圏の Yoneda と二重反転の厳密な前合成を使う。
規約：元の全関手圏を core に置き換えない。
使われ方：実単位族の表現可能性から反変の随伴関手を回収する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Duality

/-- 概要：元の圏の反対から共変表現可能関手の全圏への実際の Yoneda 写像。
方針：反対圏の Yoneda の後に二重反転の逆同型による前合成を行う。
規約：全自然変換と高次単体に作用する。
使われ方：対ごとの右随伴を表現可能関手から回収する。 -/
def pairCovariantYoneda (B : SSet.{u}) [Quasicategory B] :
    (SSet.uliftFunctor.{u + 1, u}).obj B.op ⟶
      (ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u} :=
  yonedaInfinityMap B.op ≫
    (pre ((SSet.uliftFunctor.{u + 1, u}).map (SSet.opFunctorCompOpFunctorIso.app B).inv)).app
      SpaceInfinity.{u}

/-- 概要：同じ共変 Yoneda 写像は元の反対圏を充満忠実に埋め込む。
方針：既存の Yoneda の充満忠実性に、同型による前合成の同値性を接続する。
規約：同値の存在や全関手圏の双対性は仮定しない。
使われ方：元の右関手の全高次の回収。 -/
lemma pairCovariantYoneda_isFullyFaithful (B : SSet.{u}) [Quasicategory B] :
    IsFullyFaithful (pairCovariantYoneda B) := by
  let e : (SSet.uliftFunctor.{u + 1, u}).obj B ≅
      (SSet.uliftFunctor.{u + 1, u}).obj B.op.op :=
    (SSet.uliftFunctor.{u + 1, u}).mapIso (SSet.opFunctorCompOpFunctorIso.app B).symm
  exact (yonedaInfinityMap_isFullyFaithful B.op).comp
    (((qCatEquivalenceOfIso e).precompose SpaceInfinity.{u}).isQCatEquivalence.isFullyFaithful)

/-- 概要：共変 Yoneda の元の二頂点の同型を実際に回収する。
方針：証明済みの充満忠実性の逆像を、元の二頂点に一度だけ構成する。
規約：実装を保持する不透明な定義であり、公理や存在仮定ではない。
使われ方：複雑な単位族の値での型の正規化を局所化する。 -/
opaque pairCovariantYonedaPreimageVertexIso (B : SSet.{u}) [Quasicategory B]
    {x y : ((SSet.uliftFunctor.{u + 1, u}).obj B.op) _⦋0⦌}
    (e : VertexIso ((pairCovariantYoneda B).app (Opposite.op ⦋0⦌) x)
      ((pairCovariantYoneda B).app (Opposite.op ⦋0⦌) y)) : VertexIso x y :=
  (pairCovariantYoneda_isFullyFaithful B).preimageVertexIso e

/-- 概要：共変 Yoneda の各頂点は元の共変表現可能関手そのもの。
方針：元の Yoneda の頂点公式を二重反転の前合成に通す。
規約：対象ごとの同型ではなく頂点の厳密な等式。
使われ方：元の右関手の表現可能性との照合。 -/
lemma pairCovariantYoneda_vertex {B : SSet.{u}} [Quasicategory B] (w : B.op _⦋0⦌) :
    (pairCovariantYoneda B).app (Opposite.op ⦋0⦌) (ULift.up w) =
      functorVertex (covariantRepresentableInfinity (SSet.opObjEquiv w)) := by
  change ((pre ((SSet.uliftFunctor.{u + 1, u}).map
    (SSet.opFunctorCompOpFunctorIso.app B).inv)).app SpaceInfinity.{u}).app (Opposite.op ⦋0⦌)
      ((yonedaInfinityMap B.op).app (Opposite.op ⦋0⦌) (ULift.up w)) = _
  rw [yonedaInfinityMap_vertex]
  rfl

/-- 概要：元の全単位族の全ての左頂点は共変 Yoneda の本質像に属する。
方針：d で選んだ右随伴が同じ固定左値を表現することを使う。
規約：全左関手族の元の頂点に対する主張。
使われ方：反変の随伴関手の実際の単体写像への持ち上げ。 -/
lemma pairUnitHomFamily_in_covariantYonedaImage (C D : PresentableInfinityObject.{u})
    (v : ((SSet.uliftFunctor.{u + 2, u + 1}).obj (PrLFunctorSpace C D)) _⦋0⦌) :
    ∃ w, Nonempty (VertexIso
      ((pairCovariantYoneda (PrRFunctorSpace D C)).app (Opposite.op ⦋0⦌) w)
      ((pairUnitHomFamily C D).app (Opposite.op ⦋0⦌) v)) := by
  obtain ⟨v⟩ := v
  let w := rightAdjointVertex v
  have a : QCatAdjunction (leftVertexFunctor v) (rightVertexFunctor w) := by
    simpa only [w, rightAdjointVertex, rightFunctorVertex, rightVertexFunctor,
      Equiv.symm_apply_apply] using chosenRightAdjunction v
  refine ⟨ULift.up (SSet.opObjEquiv.symm w), ?_⟩
  rw [pairCovariantYoneda_vertex, pairUnitHomFamily_vertex, Equiv.apply_symm_apply]
  exact ⟨pairUnitHomAtLeft_representationIso v w a⟩

end SerrePositivity.InfinityCategories.F2.Presentable.Duality
