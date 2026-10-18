module
public import SerrePositivity.InfinityCategories.Stable.JoinAssociatorMiddle

/-! # Join の結合同型と後二因子の包含

概要：join の結合同型は後二因子を含める射と可換である。
方針：第一因子の切断が零であることを補った join の表示で計算する。
規約：因子と次数は任意。使われ方：始対象の下の図式から始対象を忘れる制限。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：第一因子を空にして組み替えると、後二因子の単体を右から含めた表示になる。
方針：外側の切断が零であることと右因子の復号式で比較する。
規約：空次数を含む。使われ方：後二因子の包含の単体的等式。 -/
lemma stableAugReassociation_rightPair (K L M : SSet.{u}) (r : ℕ) (s : StableAugJoin L M r) :
    stableAugReassociationEquiv K L M r (stableAugJoinHom (joinInr K L) (𝟙 M) r s) =
      stableAugJoinInr K (join L M) r ((stableAugJoinEquiv L M r).symm s) := by
  let t := stableAugJoinHom (joinInr K L) (𝟙 M) r s
  let ab := stableAugJoinEquiv K L t.1.val t.2.1
  have hab : ab = stableAugJoinInr K L s.1.val s.2.1 := stableAugJoinEquiv_inr _ _ _ _
  have ha : ab.1.val = 0 := congrArg (fun z => z.1.val) hab
  refine stableAugJoin_hext _ _ ha ?_ ?_
  · change HEq ab.2.1 (show Join.augObj K 0 from PUnit.unit)
    exact stableAugJoin_left_heq hab
  · change HEq (stableAugReassociationEquiv K L M r t).2.2
      ((stableAugJoinEquiv L M r).symm s)
    apply stableAugJoinEquiv_heq (by omega : r - ab.1.val = r)
    rw [stableAugReassociation_right_decode, Equiv.apply_symm_apply]
    apply stableAugJoin_hext_total (by omega : r - ab.1.val = r)
    · change s.1.val - ab.1.val = s.1.val
      rw [ha, Nat.sub_zero]
    · exact stableAugJoin_right_heq hab
    · refine (cast_heq _ _).trans ?_
      exact heq_of_eq (Join.augHom_id M _ _)

/-- 概要：結合同型は後二因子の包含と可換。
方針：補った各次数の切断表示の計算を単体集合の射へ戻す。
規約：三因子の射の厳密な等号。使われ方：二重 coslice の射影の比較。 -/
lemma stableJoinAssociator_rightPair (K L M : SSet.{u}) :
    joinMap (joinInr K L) (𝟙 M) ≫ (stableJoinAssociator K L M).hom =
      joinInr K (join L M) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply (stableAugJoinEquiv K (join L M) (n + 1)).injective
  change (stableAugJoinEquiv K (join L M) (n + 1))
    ((stableAugJoinEquiv K (join L M) (n + 1)).symm
      (stableAugReassociationEquiv K L M (n + 1)
        (stableAugJoinEquiv (join K L) M (n + 1)
          (Join.augHom (joinMap (joinInr K L) (𝟙 M)) (n + 1) s)))) = _
  rw [Equiv.apply_symm_apply, stableAugJoinEquiv_hom, stableAugReassociation_rightPair]
  rw [Equiv.symm_apply_apply]
  exact (stableAugJoinEquiv_inr K (join L M) (n + 1) s).symm

/-- 概要：逆結合同型は後二因子の右包含を保つ。
方針：順方向の式に逆同型を合成する。
規約：射の厳密な等号。使われ方：始対象の下の図式の余錐の射影。 -/
lemma stableJoinAssociator_rightPair_inv (K L M : SSet.{u}) :
    joinInr K (join L M) ≫ (stableJoinAssociator K L M).inv =
      joinMap (joinInr K L) (𝟙 M) := by
  rw [← stableJoinAssociator_rightPair, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end SerrePositivity.InfinityCategories
