module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.NerveCone
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
概要：c の下の射列を c を先頭に置いた通常の射列にする。
方針：先頭の構造射を前置し Under の可換性で自然性を証明する。
規約：同じ宇宙の小さい圏を扱い、始対象性は仮定しない。
使われ方：B5 の pointwise Kan の古典比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison

variable {C : Type u} [Category.{u} C] (c : C)

/-- 概要：Under の射列の先頭に c を前置する。
方針：忘却した射列の最初の構造射を前置する。
規約：新しい零番目の対象は c。
使われ方：coslice と通常の Under の比較。 -/
def nerveUnderChain {n : ℕ} (F : ComposableArrows (Under c) n) : ComposableArrows C (n + 1) :=
  ComposableArrows.precomp (F ⋙ Under.forget c) (F.obj 0).hom

/-- 概要：前置した c から各対象への射は元の構造射。
方針：Under の可換三角形を使う。
規約：任意の後続頂点についての式。
使われ方：射列の自然性と逆構成の検証。 -/
lemma nerveUnderChain_map_zero_succ {n : ℕ}
    (F : ComposableArrows (Under c) n) (j : Fin (n + 1)) :
    (nerveUnderChain c F).map
      (homOfLE (show (0 : Fin (n + 2)) ≤ j.succ by simp)) = (F.obj j).hom := by
  obtain ⟨_ | j, hj⟩ := j
  · rfl
  · exact Under.w (F.map (homOfLE (show (0 : Fin (n + 1)) ≤ ⟨j + 1, hj⟩ by simp)))

/-- 概要：前置した射列は始点を固定した添字変更に自然。
方針：尾部と最初の射に射列の拡張性を使う。
規約：prependOrderHom は新しい始点を保つ。
使われ方：nerve から coslice への射の自然性。 -/
lemma nerveUnderChain_naturality {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) (F : (nerve (Under c)) _⦋n⦌) :
    (nerve C).map (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom α.toOrderHom)).op
      (nerveUnderChain c F) =
      nerveUnderChain c ((nerve (Under c)).map α.op F) := by
  refine ComposableArrows.ext_succ ?_ ?_ ?_
  · rfl
  · rfl
  · simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    exact nerveUnderChain_map_zero_succ c F (α.toOrderHom 0)

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
