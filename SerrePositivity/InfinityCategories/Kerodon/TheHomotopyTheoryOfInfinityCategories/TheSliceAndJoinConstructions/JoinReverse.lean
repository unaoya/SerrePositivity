module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinReverseNaturality

/-! # join の反転同型

概要：join 全体の反転は、反転した因子の順序を交換した join と同型。
方針：各次数の同値を単体作用の自然性で束ねる。
規約：順方向は (K⋆L).op から L.op⋆K.op。
使われ方：S4 の押し出しと引き戻し、および slice と coslice の比較。

対応節は Kerodon 4.3（Tag 015M）。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

/-- 概要：join 全体の反転を左右交換した反転因子の join へ写す射。
方針：補った各次数の反転の同値を使う。
規約：空次数の計算は自然性の証明に含まれる。
使われ方：join の反転同型の順方向。 -/
def stableJoinReverseHom (K L : SSet.{u}) : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K L).op ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join L.op K.op where
  app n := ↾(_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableAugJoinReverseEquiv K L (n.unop.len + 1))
  naturality {n m} α := by
    obtain ⟨⟨n⟩⟩ := n
    obtain ⟨⟨m⟩⟩ := m
    apply ConcreteCategory.hom_ext
    intro s
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableAugJoinReverseEquiv_naturality K L α.unop.toOrderHom s

/-- 概要：join の反転の射は同型。
方針：各次数が同値なので全単射性を使う。
規約：任意の二因子。使われ方：反転同型の構成。 -/
instance stableJoinReverseHom_isIso (K L : SSet.{u}) : IsIso (stableJoinReverseHom K L) := by
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  rintro ⟨⟨n⟩⟩
  exact (isIso_iff_bijective _).mpr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableAugJoinReverseEquiv K L (n + 1)).bijective

/-- 概要：join の反転は因子を反転して順序を交換した join と同型。
方針：切断の補数と二因子の交換を各次数で行い、自然性で束ねる。
規約：追加の仮定なし。使われ方：S4 の双対化。 -/
def stableJoinReverseIso (K L : SSet.{u}) : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K L).op ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join L.op K.op :=
  asIso (stableJoinReverseHom K L)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
