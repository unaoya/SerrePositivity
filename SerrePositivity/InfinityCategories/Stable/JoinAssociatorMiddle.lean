module
public import SerrePositivity.InfinityCategories.Stable.JoinAssociatorBoundary

/-! # join の結合同型と中間因子の除去

概要：第一・第三因子からの包含も結合同型と可換である。
方針：第二因子の空区間を切断表示で計算する。
規約：三因子は任意。使われ方：S4 の余錐全体から基底の coslice への制限。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：頂点数零の補った単体は唯一の空単体と異種等式で一致する。
方針：頂点数を零へ置換して一点性を使う。
規約：等式による移送を明示する。使われ方：空の中間因子の計算。 -/
lemma stableAugEmpty_heq (K : SSet.{u}) {r : ℕ} (hr : r = 0) (x : Join.augObj K r) :
    HEq x (show Join.augObj K 0 from PUnit.unit) := by
  subst r
  exact heq_of_eq (@Subsingleton.elim PUnit inferInstance _ _)

/-- 概要：中間因子を空にしてから組み替えると、その空区間は右 join の左端に残る。
方針：左包含の切断表示から外側の切断と空の第二因子を復元する。
規約：補った各次数での式。使われ方：余錐全体から基底への制限。 -/
lemma stableAugReassociation_middle (K L M : SSet.{u}) (r : ℕ) (s : StableAugJoin K M r) :
    stableAugReassociationEquiv K L M r (stableAugJoinHom (joinInl K L) (𝟙 M) r s) =
      stableAugJoinHom (𝟙 K) (joinInr L M) r s := by
  let t := stableAugJoinHom (joinInl K L) (𝟙 M) r s
  let ab := stableAugJoinEquiv K L t.1.val t.2.1
  have hab : ab = stableAugJoinInl K L s.1.val s.2.1 := stableAugJoinEquiv_inl _ _ _ _
  have ha : ab.1.val = s.1.val := congrArg (fun z ↦ z.1.val) hab
  refine stableAugJoin_hext _ _ ha ?_ ?_
  · change HEq ab.2.1 (Join.augHom (𝟙 K) s.1.val s.2.1)
    exact (stableAugJoin_left_heq hab).trans (heq_of_eq (Join.augHom_id K _ _).symm)
  · change HEq (stableAugReassociationEquiv K L M r t).2.2
      (Join.augHom (joinInr L M) (r - s.1.val) s.2.2)
    apply stableAugJoinEquiv_heq (congrArg (fun a ↦ r - a) ha)
    rw [stableAugReassociation_right_decode, stableAugJoinEquiv_inr]
    apply stableAugJoin_hext_total (congrArg (fun a ↦ r - a) ha)
    · exact (congrArg (fun a ↦ s.1.val - a) ha).trans (Nat.sub_self _)
    · exact (stableAugJoin_right_heq hab).trans (stableAugEmpty_heq L (Nat.sub_self _) _)
    · refine (cast_heq _ _).trans ?_
      exact heq_of_eq (Join.augHom_id M _ _)

/-- 概要：結合同型は第一・第三因子からの包含と可換。
方針：各次数で中間因子が空である場合の組み替えを使う。
規約：単体的な射の等式。使われ方：coslice 制限の join 上の計算。 -/
lemma stableJoinAssociator_middle (K L M : SSet.{u}) :
    joinMap (joinInl K L) (𝟙 M) ≫ (stableJoinAssociator K L M).hom =
      joinMap (𝟙 K) (joinInr L M) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply (stableAugJoinEquiv K (join L M) (n + 1)).injective
  change (stableAugJoinEquiv K (join L M) (n + 1))
    ((stableAugJoinEquiv K (join L M) (n + 1)).symm
      (stableAugReassociationEquiv K L M (n + 1)
        (stableAugJoinEquiv (join K L) M (n + 1)
          (Join.augHom (joinMap (joinInl K L) (𝟙 M)) (n + 1) s)))) = _
  rw [Equiv.apply_symm_apply, stableAugJoinEquiv_hom, stableAugReassociation_middle]
  exact (stableAugJoinEquiv_hom (𝟙 K) (joinInr L M) (n + 1) s).symm

/-- 概要：右 join の第三因子への制限の後で逆結合すると、第一因子の包含に沿う制限になる。
方針：中間因子の包含の式に逆同型を合成する。
規約：射の厳密な等式。使われ方：余極限 coslice 制限の計算。 -/
lemma stableJoinAssociator_middle_inv (K L M : SSet.{u}) :
    joinMap (𝟙 K) (joinInr L M) ≫ (stableJoinAssociator K L M).inv =
      joinMap (joinInl K L) (𝟙 M) := by
  rw [← stableJoinAssociator_middle, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end SerrePositivity.InfinityCategories
