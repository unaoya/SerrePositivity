module
public import SerrePositivity.InfinityCategories.Stable.JoinAssociatorFactors

/-! # join の結合同型と因子の包含

概要：結合同型と左右の因子の包含の可換性を示す。
方針：空次数を含む包含の切断表示を計算する。
規約：因子の集合上の一致でなく、単体的な射の等式を使う。
使われ方：S4 の二重 coslice の固定図式と射影の計算。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：補った左因子の単体を全区間の切断で join に含める。
方針：右の空単体を補う。規約：頂点数零も含む。
使われ方：結合同型の左因子の固定条件。 -/
def stableAugJoinInl (K L : SSet.{u}) (r : ℕ) (x : Join.augObj K r) : StableAugJoin K L r :=
  ⟨⟨r, by omega⟩, x, by simp only [Nat.sub_self, Join.augObj]; exact PUnit.unit⟩

/-- 概要：補った右因子の単体を零の切断で join に含める。
方針：左の空単体を補う。規約：頂点数零も含む。
使われ方：結合同型の右因子の固定条件。 -/
def stableAugJoinInr (K L : SSet.{u}) (r : ℕ) (x : Join.augObj L r) : StableAugJoin K L r :=
  ⟨⟨0, by omega⟩, PUnit.unit, x⟩

/-- 概要：補った左包含を切断表示で読むと全区間の切断になる。
方針：頂点数零と非零に分けて定義を計算する。
規約：既存の joinInl との厳密な一致。使われ方：左因子に沿う組み替え。 -/
lemma stableAugJoinEquiv_inl (K L : SSet.{u}) (r : ℕ) (x : Join.augObj K r) :
    stableAugJoinEquiv K L r (Join.augHom (joinInl K L) r x) = stableAugJoinInl K L r x := by
  cases r <;> rfl

/-- 概要：補った右包含を切断表示で読むと零の切断になる。
方針：頂点数零と非零に分けて定義を計算する。
規約：既存の joinInr との厳密な一致。使われ方：右因子に沿う組み替え。 -/
lemma stableAugJoinEquiv_inr (K L : SSet.{u}) (r : ℕ) (x : Join.augObj L r) :
    stableAugJoinEquiv K L r (Join.augHom (joinInr K L) r x) = stableAugJoinInr K L r x := by
  cases r <;> rfl

/-- 概要：左の二因子を含めてから組み替えると第二因子だけをその左包含で写す。
方針：右側の空区間を最後の因子の空単体として保つ。
規約：補った各次数での等式。使われ方：二重 coslice の固定図式。 -/
lemma stableAugReassociation_inl (K L M : SSet.{u}) (r : ℕ)
    (s : Join.augObj (join K L) r) :
    stableAugReassociationEquiv K L M r (stableAugJoinInl (join K L) M r s) =
      stableAugJoinHom (𝟙 K) (joinInl L M) r (stableAugJoinEquiv K L r s) := by
  let t := stableAugJoinInl (join K L) M r s
  let ab := stableAugJoinEquiv K L t.1.val t.2.1
  refine stableAugJoin_hext _ _ rfl ?_ ?_
  · exact heq_of_eq (Join.augHom_id K ab.1.val ab.2.1).symm
  · change HEq (stableAugReassociationEquiv K L M r t).2.2
      (Join.augHom (joinInl L M) (r - ab.1.val) ab.2.2)
    apply stableAugJoinEquiv_heq (r := r - ab.1.val) (r' := r - ab.1.val) rfl
    rw [stableAugReassociation_right_decode, stableAugJoinEquiv_inl]
    apply heq_of_eq
    refine stableAugJoin_hext _ _ rfl HEq.rfl ?_
    apply heq_of_eq
    exact @Subsingleton.elim (Join.augObj M (r - ab.1.val - (r - ab.1.val)))
      (by simp only [Nat.sub_self, Join.augObj]; infer_instance) _ _

/-- 概要：結合同型と左の二因子の包含は可換。
方針：各次数で切断表示へ移し、補った左包含の組み替えを使う。
規約：単体的な射の厳密な等式。使われ方：二重 coslice の固定条件。 -/
lemma stableJoinAssociator_inl (K L M : SSet.{u}) :
    joinInl (join K L) M ≫ (stableJoinAssociator K L M).hom =
      joinMap (𝟙 K) (joinInl L M) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply (stableAugJoinEquiv K (join L M) (n + 1)).injective
  change (stableAugJoinEquiv K (join L M) (n + 1))
    ((stableAugJoinEquiv K (join L M) (n + 1)).symm
      (stableAugReassociationEquiv K L M (n + 1)
        (stableAugJoinEquiv (join K L) M (n + 1)
          (Join.augHom (joinInl (join K L) M) (n + 1) s)))) = _
  rw [Equiv.apply_symm_apply, stableAugJoinEquiv_inl, stableAugReassociation_inl]
  exact (stableAugJoinEquiv_hom (𝟙 K) (joinInl L M) (n + 1) s).symm

/-- 概要：結合同型は右端の因子の包含を保つ。
方針：各単体で二つの切断を零として計算する。
規約：右端の因子の射の厳密な等式。使われ方：coslice の射影の比較。 -/
lemma stableJoinAssociator_inr (K L M : SSet.{u}) :
    joinInr (join K L) M ≫ (stableJoinAssociator K L M).hom =
      joinInr L M ≫ joinInr K (join L M) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  rfl

end SerrePositivity.InfinityCategories
