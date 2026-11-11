module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PairUnitCorrespondence

/-!
概要：二対象の母対応の零単体から、元の単位と関手の頂点を回収する。
方針：零単体の twisted arrow が零単体そのものである厳密な同型を使う。
規約：全自然変換を持つ母空間を core に変更しない。
使われ方：実単位の随伴条件を頂点上に課す準備。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：零単体の twisted arrow における唯一の頂点。
方針：twisted 重みから終対象である零単体への唯一の射を使う。
規約：宇宙を変えずに定義する。
使われ方：単位図式の零単体での評価。 -/
def twistedZeroPoint : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrow (Δ[0] : SSet.{u})) _⦋0⦌ :=
  SSet.stdSimplex.isTerminalObj₀.from _

/-- 概要：零単体の twisted arrow は元の零単体と厳密に同型。
方針：右端射影と唯一の頂点の定値写像を両逆にする。
規約：quasicategory 同値に弱めない。
使われ方：頂点の単位図式から元の実単位を取り出す。 -/
def twistedZeroIso : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrow (Δ[0] : SSet.{u}) ≅ (Δ[0] : SSet.{u}) where
  hom := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight _
  inv := SSet.const twistedZeroPoint
  hom_inv_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  inv_hom_id := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

/-- 概要：twisted 零単体からの二つの射は唯一の頂点での値が同じなら等しい。
方針：零単体との厳密な同型で前合成して Yoneda の単射性を使う。
規約：標的の充填性は不要。
使われ方：指定単位から対応頂点を構成するときの可換条件。 -/
lemma twistedZeroMap_ext {X : SSet.{u}}
    (f g : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrow (Δ[0] : SSet.{u}) ⟶ X)
    (h : f.app (Opposite.op ⦋0⦌) twistedZeroPoint =
      g.app (Opposite.op ⦋0⦌) twistedZeroPoint) : f = g := by
  apply (cancel_epi twistedZeroIso.inv).mp
  apply SSet.yonedaEquiv.injective
  exact h

/-- 概要：母対応の頂点が持つ実際の単位族の零単体。
方針：twisted 零単体の逆同型の後に指定された単位族を評価する。
規約：単位を新しく選択しない。
使われ方：随伴条件の頂点述語。 -/
def twistedPairUnitVertex {A B S T : SSet.{u}} {q : S ⟶ T} {b : A ⊗ B ⟶ T}
    (x : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.twistedPairLift q b _⦋0⦌) : S _⦋0⦌ :=
  x.unit.app (Opposite.op ⦋0⦌) twistedZeroPoint

/-- 概要：零単体における逆向きの族の評価は、元の右頂点の反転解除。
方針：零単体の唯一の頂点で射の反転を計算する。
規約：元の右関手頂点を保持する。
使われ方：単位の終点の元の LR との同定。 -/
lemma unopPairFamily_vertex {B : SSet.{u}} (r : (Δ[0] : SSet.{u}) ⟶ B.op)
    (v : (Δ[0] : SSet.{u}).op _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.unopPairFamily r).app (Opposite.op ⦋0⦌) v =
      SSet.opObjEquiv (SSet.yonedaEquiv r) := by
  have hv : v = SSet.opObjEquiv.symm
      (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}))) := by
    apply SSet.opObjEquiv.injective
    apply SSet.yonedaEquiv.symm.injective
    exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [hv]
  rfl

/-- 概要：母対応の実単位の終点は元の左右の関手の共同評価。
方針：単位図式の可換条件を唯一の twisted 零頂点で評価する。
規約：左右の頂点を同型で置き換えない。
使われ方：元の単位による随伴判定への接続。 -/
lemma twistedPairUnitVertex_projection {A B S T : SSet.{u}} {q : S ⟶ T}
    {b : A ⊗ B ⟶ T} (x : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.twistedPairLift q b _⦋0⦌) :
    q.app (Opposite.op ⦋0⦌) (twistedPairUnitVertex x) =
      b.app (Opposite.op ⦋0⦌)
        (SSet.yonedaEquiv x.left, SSet.opObjEquiv (SSet.yonedaEquiv x.right)) := by
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app x.condition (Opposite.op ⦋0⦌)) twistedZeroPoint
  change q.app (Opposite.op ⦋0⦌) (twistedPairUnitVertex x) =
    b.app (Opposite.op ⦋0⦌)
      (x.left.app (Opposite.op ⦋0⦌) ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight _).app (Opposite.op ⦋0⦌) twistedZeroPoint),
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.unopPairFamily x.right).app (Opposite.op ⦋0⦌)
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft _).app (Opposite.op ⦋0⦌) twistedZeroPoint)) at h
  rw [unopPairFamily_vertex] at h
  have hz : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight (Δ[0] : SSet.{u})).app (Opposite.op ⦋0⦌) twistedZeroPoint =
      SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})) := by
    apply SSet.yonedaEquiv.symm.injective
    exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [hz] at h
  exact h

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
