module
public import SerrePositivity.InfinityCategories.Stable.JoinReassociationNaturality

/-! # join の結合同型

概要：三因子の join の二つの括弧を単体集合の同型で比較する。
方針：各次数の切断表示の同値を、引き戻しの自然性によって束ねる。
規約：任意の単体集合を因子にできる。使われ方：S4 の二重 coslice の表示。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：三因子の補った join の同値は順序写像の引き戻しと可換。
方針：切断表示の自然性と組み替えの自然性を合成する。
規約：空区間を含む。使われ方：join の結合同型の自然性。 -/
lemma stableAugJoinAssociatorEquiv_naturality (K L M : SSet.{u}) {m n : ℕ}
    (α : Fin m →o Fin n) (s : Join.augObj (join (join K L) M) n) :
    stableAugJoinAssociatorEquiv K L M m (Join.augMap (join (join K L) M) α s) =
      Join.augMap (join K (join L M)) α (stableAugJoinAssociatorEquiv K L M n s) := by
  apply (stableAugJoinEquiv K (join L M) m).injective
  change (stableAugJoinEquiv K (join L M) m)
    ((stableAugJoinEquiv K (join L M) m).symm
      (stableAugReassociationEquiv K L M m
        (stableAugJoinEquiv (join K L) M m (Join.augMap (join (join K L) M) α s)))) = _
  rw [Equiv.apply_symm_apply]
  rw [stableAugJoinEquiv_naturality K (join L M)]
  change _ = stableAugJoinMap K (join L M) α
    ((stableAugJoinEquiv K (join L M) n)
      ((stableAugJoinEquiv K (join L M) n).symm
        (stableAugReassociationEquiv K L M n (stableAugJoinEquiv (join K L) M n s))))
  rw [Equiv.apply_symm_apply, stableAugJoinEquiv_naturality, stableAugReassociation_naturality]

/-- 概要：左に括弧を付けた三因子の join を右に括弧を付けた join へ写す射。
方針：補った各次数の組み替えを自然性で束ねる。
規約：各次数の写像は同値。使われ方：二重 coslice の組み替え。 -/
def stableJoinAssociatorHom (K L M : SSet.{u}) : join (join K L) M ⟶ join K (join L M) where
  app n := ↾(stableAugJoinAssociatorEquiv K L M (n.unop.len + 1))
  naturality {n m} α := by
    obtain ⟨⟨n⟩⟩ := n
    obtain ⟨⟨m⟩⟩ := m
    apply ConcreteCategory.hom_ext
    intro s
    exact stableAugJoinAssociatorEquiv_naturality K L M α.unop.toOrderHom s

/-- 概要：join の組み替えの射は同型。
方針：各次数の全単射性で判定する。
規約：因子には追加の仮定を置かない。使われ方：結合同型の構成。 -/
instance stableJoinAssociatorHom_isIso (K L M : SSet.{u}) :
    IsIso (stableJoinAssociatorHom K L M) := by
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  rintro ⟨⟨n⟩⟩
  exact (isIso_iff_bijective _).mpr (stableAugJoinAssociatorEquiv K L M (n + 1)).bijective

/-- 概要：単体集合の join の結合同型。
方針：頂点数ごとの切断の組み替えを自然性とともに束ねる。
規約：順方向は (K⋆L)⋆M から K⋆(L⋆M)。
使われ方：S4 の二重 coslice と一段の coslice の比較。 -/
def stableJoinAssociator (K L M : SSet.{u}) : join (join K L) M ≅ join K (join L M) :=
  asIso (stableJoinAssociatorHom K L M)

end SerrePositivity.InfinityCategories
