module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKan
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.Nerve

/-!
概要：射列の各初区間を終点の over 圏へ持ち上げ、Bousfield–Kan 重みの単体を作る。
方針：各頂点から区間の終点への射を添え、その自然性を使う。
規約：初区間は終点自身を含み、添字 i に標準 i 単体を対応させる。
使われ方：Kerodon 5.3.3.1（Tag 025X）、7.5.3.12（Tag 03B1） の weighted nerve の切断と重み付き end の比較。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
variable {I : Type u} [SmallCategory I]

/-- 概要：射列の初区間から、その終点に定値な図式への自然変換。
方針：各頂点から指定の終点への大小関係を射列で写す。
規約：初区間の頂点は元の添字の値を保つ。
使われ方：Kerodon 5.3.3.1（Tag 025X）、7.5.3.12（Tag 03B1） の over 圏への持ち上げ。 -/
def prefixTerminalTransformation {n : ℕ} (σ : ComposableArrows I n) (i : Fin (n + 1)) :
    (SimplexCategory.toCat.map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion i.val n (Nat.le_of_lt_succ i.isLt))).toFunctor ⋙ σ ⟶
        (Functor.const (Fin (i.val + 1))).obj (σ.obj i) where
  app k := σ.map (homOfLE (show _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixVertex i k ≤ i from
    Nat.le_of_lt_succ k.isLt))
  naturality k l f := by
    change σ.map _ ≫ σ.map _ = σ.map _ ≫ 𝟙 _
    rw [Category.comp_id, ← σ.map_comp]
    rfl

/-- 概要：射列の初区間を終点の over 圏の射列へ持ち上げる。
方針：終点への自然変換を Over.lift に渡す。
規約：射列の長さは終点 i の自然数の値。
使われ方：Kerodon 5.3.3.1（Tag 025X）、7.5.3.12（Tag 03B1） の初区間の重みの標準単体。 -/
def prefixOverChain {n : ℕ} (σ : ComposableArrows I n) (i : Fin (n + 1)) :
    ComposableArrows (Over (σ.obj i)) i.val :=
  Over.lift _ (prefixTerminalTransformation σ i)

/-- 概要：初区間の over 圏の射列を忘れると元の射列の初区間になる。
方針：Over.lift の対象と射の定義を読む。
規約：標準の初区間の包含で制限する。
使われ方：Kerodon 5.3.3.1（Tag 025X）、7.5.3.12（Tag 03B1） の底の射列の回収。 -/
lemma prefixOverChain_forget {n : ℕ} (σ : ComposableArrows I n) (i : Fin (n + 1)) :
    prefixOverChain σ i ⋙ Over.forget (σ.obj i) =
      (SimplexCategory.toCat.map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion i.val n (Nat.le_of_lt_succ i.isLt))).toFunctor ⋙ σ := rfl

/-- 概要：初区間の over 圏の標準単体は、その終点を後へ移す射と可換である。
方針：対象は射列の合成則、射は over の忘却関手の忠実性で比較する。
規約：i ≤ j のとき終点を σ(i) から σ(j) へ後合成する。
使われ方：Kerodon 5.3.3.1（Tag 025X）、7.5.3.12（Tag 03B1） の初区間の重みの自然性。 -/
lemma prefixOverChain_inclusion {n : ℕ} (σ : ComposableArrows I n)
    {i j : Fin (n + 1)} (h : i ≤ j) :
    (SimplexCategory.toCat.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion i.val j.val h)).toFunctor ⋙
        prefixOverChain σ j =
      prefixOverChain σ i ⋙ Over.map (σ.map (homOfLE h)) := by
  refine CategoryTheory.Functor.ext (fun k => ?_) ?_
  · change Over.mk (σ.map (homOfLE _)) =
      Over.mk (σ.map (homOfLE _) ≫ σ.map (homOfLE h))
    rw [← σ.map_comp]
    rfl
  · intro k l f
    apply (Over.forget (σ.obj j)).map_injective
    simp
    rfl

/-- 概要：初区間の標準単体は終点を移す射と単体集合の射として可換。
方針：射列の包含の公式を Yoneda の自然性で移す。
規約：共変な Bousfield–Kan 重みの遷移を使う。
使われ方：Kerodon 5.3.3.1（Tag 025X）、7.5.3.12（Tag 03B1） の切断の係数の自然性。 -/
lemma prefixOverChain_yoneda_inclusion {n : ℕ} (σ : ComposableArrows I n)
    {i j : Fin (n + 1)} (h : i ≤ j) :
    stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion i.val j.val h) ≫
        SSet.yonedaEquiv.symm (prefixOverChain σ j) =
      SSet.yonedaEquiv.symm (prefixOverChain σ i) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I).map (σ.map (homOfLE h)) := by
  rw [SSet.yonedaEquiv_symm_naturality_left, SSet.yonedaEquiv_symm_comp]
  exact congrArg SSet.yonedaEquiv.symm (prefixOverChain_inclusion σ h)

/-- 概要：射列の各初区間は Bousfield–Kan 重みへの標準の自然変換を与える。
方針：各成分を over 圏への持ち上げの標準単体とし、初区間の包含の式を使う。
規約：始域は weighted nerve の初区間の重み。
使われ方：Kerodon 5.3.3.1（Tag 025X）、7.5.3.12（Tag 03B1） の重み付き end から切断への構成。 -/
def prefixOverWeight {n : ℕ} (σ : ComposableArrows I n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight n ⟶ σ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I where
  app i := SSet.yonedaEquiv.symm (prefixOverChain σ i)
  naturality _ _ f := prefixOverChain_yoneda_inclusion σ (leOfHom f)

/-- 概要：初区間の over 圏の持ち上げは任意の単体作用素の初区間への制限と可換。
方針：両側の対象は同じ射を表し、射の左成分も定義で一致する。
規約：終点は α(i) に移り、面と退化を同時に扱う。
使われ方：Kerodon 5.3.3.1（Tag 025X）、7.5.3.12（Tag 03B1） の切断を定める単体作用の整合性。 -/
lemma prefixOverChain_restriction {m n : SimplexCategory} (α : m ⟶ n)
    (σ : ComposableArrows I n.len) (i : Fin (m.len + 1)) :
    prefixOverChain ((SimplexCategory.toCat.map α).toFunctor ⋙ σ) i =
      (SimplexCategory.toCat.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixRestriction α i)).toFunctor ⋙
        prefixOverChain σ (α.toOrderHom i) := rfl

/-- 概要：over 圏の標準単体の制限は底の単体作用素と可換。
方針：射列の制限の等式を Yoneda の自然性で移す。
規約：標的は σ(α(i)) の over 圏の nerve。
使われ方：Kerodon 5.3.3.1（Tag 025X）、7.5.3.12（Tag 03B1） の係数の面と退化の式。 -/
lemma prefixOverChain_yoneda_restriction {m n : SimplexCategory} (α : m ⟶ n)
    (σ : ComposableArrows I n.len) (i : Fin (m.len + 1)) :
    (SSet.yonedaEquiv (X := nerve (Over (σ.obj (α.toOrderHom i))))
      (n := ⦋i.val⦌)).symm
        (prefixOverChain ((SimplexCategory.toCat.map α).toFunctor ⋙ σ) i) =
      stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixRestriction α i) ≫
        (SSet.yonedaEquiv (X := nerve (Over (σ.obj (α.toOrderHom i))))
          (n := ⦋(α.toOrderHom i).val⦌)).symm (prefixOverChain σ (α.toOrderHom i)) := by
  rw [SSet.yonedaEquiv_symm_naturality_left]
  rfl

/-- 概要：初区間から Bousfield–Kan 重みへの自然変換は底の単体作用素と可換。
方針：各成分で標準単体の制限の式を使う。
規約：元の射列と係数の図式を同じ順序関手で引き戻す。
使われ方：Kerodon 5.3.3.1（Tag 025X）、7.5.3.12（Tag 03B1） の重み付き end と切断の比較。 -/
lemma prefixOverWeight_restriction {m n : SimplexCategory} (α : m ⟶ n)
    (σ : ComposableArrows I n.len) :
    prefixOverWeight ((SimplexCategory.toCat.map α).toFunctor ⋙ σ) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeightRestriction α ≫
        Functor.whiskerLeft (SimplexCategory.toCat.map α).toFunctor (prefixOverWeight σ) := by
  apply NatTrans.ext
  funext i
  exact prefixOverChain_yoneda_restriction α σ i

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
