module

public import SerrePositivity.InfinityCategories.HomotopyLimits.JoinTripleMaps

/-!
概要：三因子の join の再結合を単体集合の同型として構成する。
方針：両括弧付けを三つの区間の共通表示へ移し、全ての単体作用との可換性を使う。
規約：順方向は (A⋆B)⋆C から A⋆(B⋆C)。空単体を補った構成で空区間を含む。
使われ方：HTT §1.2.8、4.2.4.1 と Kerodon 7.4.1.6 の反復 slice の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 概要：左括弧の join の補った単体を三つの区間で表示する。
方針：外側の join の和表示と左因子の展開を合成する。
規約：n は頂点数であり零も含む。
使われ方：Kerodon §4.3.5 の再結合の自然性の共通模型。 -/
def leftJoinTripleEncoding (A B C : SSet.{u}) (n : ℕ) :
    Join.augObj (join (join A B) C) n ≃ joinTripleSimplex A B C n :=
  (augmentedJoinSumEquiv (join A B) C n).trans (leftJoinSumTripleEquiv A B C n)

/-- 概要：右括弧の join の補った単体を三つの区間で表示する。
方針：外側の join の和表示と右因子の展開を合成する。
規約：三つの頂点数の和の括弧付けは共通表示に合わせる。
使われ方：Kerodon §4.3.5 の再結合の自然性の共通模型。 -/
def rightJoinTripleEncoding (A B C : SSet.{u}) (n : ℕ) :
    Join.augObj (join A (join B C)) n ≃ joinTripleSimplex A B C n :=
  (augmentedJoinSumEquiv A (join B C) n).trans (rightJoinSumTripleEquiv A B C n)

/-- 概要：左括弧の共通表示への全単射は全ての順序写像による制限と可換。
方針：外側の二因子の自然性と、左括弧の内側の作用の同定を合成する。
規約：空の始域と終域も含む。
使われ方：HTT §1.2.8 の再結合の面・退化との可換性。 -/
lemma leftJoinTripleEncoding_map (A B C : SSet.{u}) {m n : ℕ}
    (α : Fin m →o Fin n) (s : Join.augObj (join (join A B) C) n) :
    leftJoinTripleEncoding A B C m (Join.augMap (join (join A B) C) α s) =
      joinTripleSimplexMap A B C α (leftJoinTripleEncoding A B C n s) := by
  change leftJoinSumTripleEquiv A B C m
      (augmentedJoinSumEquiv (join A B) C m (Join.augMap (join (join A B) C) α s)) = _
  rw [augmentedJoinSumEquiv_map]
  have h := joinTripleSimplexMap_left A B C α
    (leftJoinSumTripleEquiv A B C n (augmentedJoinSumEquiv (join A B) C n s))
  simpa only [Equiv.symm_apply_apply, leftJoinTripleEncoding, Equiv.trans_apply] using h

/-- 概要：右括弧の共通表示への全単射は全ての順序写像による制限と可換。
方針：外側の二因子の自然性と、右括弧の内側の作用の同定を合成する。
規約：空区間の移送を含む実際の構成について述べる。
使われ方：HTT §1.2.8 の再結合の面・退化との可換性。 -/
lemma rightJoinTripleEncoding_map (A B C : SSet.{u}) {m n : ℕ}
    (α : Fin m →o Fin n) (s : Join.augObj (join A (join B C)) n) :
    rightJoinTripleEncoding A B C m (Join.augMap (join A (join B C)) α s) =
      joinTripleSimplexMap A B C α (rightJoinTripleEncoding A B C n s) := by
  change rightJoinSumTripleEquiv A B C m
      (augmentedJoinSumEquiv A (join B C) m (Join.augMap (join A (join B C)) α s)) = _
  rw [augmentedJoinSumEquiv_map]
  have h := joinTripleSimplexMap_right A B C α
    (rightJoinSumTripleEquiv A B C n (augmentedJoinSumEquiv A (join B C) n s))
  simpa only [Equiv.symm_apply_apply, rightJoinTripleEncoding, Equiv.trans_apply] using h

/-- 概要：join の次数ごとの再結合の全単射は全ての面・退化と可換。
方針：右括弧の共通表示への全単射で検出し、両側の表示の自然性を使う。
規約：構成済みの joinAssociatorSimplexEquiv そのものの自然性。
使われ方：Kerodon §4.3.5 の join の結合の単体集合の同型への昇格。 -/
lemma joinAssociatorSimplexEquiv_naturality (A B C : SSet.{u}) {m n : ℕ}
    (α : ⦋m⦌ ⟶ ⦋n⦌) (s : (join (join A B) C) _⦋n⦌) :
    joinAssociatorSimplexEquiv A B C m ((join (join A B) C).map α.op s) =
      (join A (join B C)).map α.op (joinAssociatorSimplexEquiv A B C n s) := by
  have he (k : ℕ) (t : (join (join A B) C) _⦋k⦌) :
      rightJoinTripleEncoding A B C (k + 1) (joinAssociatorSimplexEquiv A B C k t) =
        leftJoinTripleEncoding A B C (k + 1) t := by
    change rightJoinTripleEncoding A B C (k + 1)
      ((rightJoinTripleEncoding A B C (k + 1)).symm
        (leftJoinTripleEncoding A B C (k + 1) t)) = _
    exact Equiv.apply_symm_apply _ _
  apply (rightJoinTripleEncoding A B C (m + 1)).injective
  rw [he]
  change _ = rightJoinTripleEncoding A B C (m + 1)
    (Join.augMap (join A (join B C)) α.toOrderHom
      (joinAssociatorSimplexEquiv A B C n s))
  rw [rightJoinTripleEncoding_map, he]
  exact leftJoinTripleEncoding_map A B C α.toOrderHom s

/-- 概要：三因子の join の二つの括弧付けは単体集合として厳密に同型。
方針：各次数の再結合の全単射を、単体作用との可換性により自然同型に束ねる。
規約：Kan 性や quasicategory 性の仮定は不要。
使われ方：HTT 4.2.4.1、Kerodon 7.4.1.6 の反復 slice と錐の図式の再結合。 -/
def joinAssociator (A B C : SSet.{u}) : join (join A B) C ≅ join A (join B C) :=
  NatIso.ofComponents (fun d ↦ (joinAssociatorSimplexEquiv A B C d.unop.len).toIso)
    (fun {d e} α ↦ by
      obtain ⟨⟨n⟩⟩ := d
      obtain ⟨⟨m⟩⟩ := e
      apply ConcreteCategory.hom_ext
      intro s
      exact joinAssociatorSimplexEquiv_naturality A B C α.unop s)

end SerrePositivity.InfinityCategories.HomotopyLimits
