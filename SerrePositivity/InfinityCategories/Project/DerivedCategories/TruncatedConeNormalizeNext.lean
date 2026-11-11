module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.TruncatedConeDegeneracyOverlap
public import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate

/-! # 次次数の錐単体の退化整合的な正規化

概要：退化単体の充填を下次数錐の標準正番号退化へ置き換える。
方針：基本退化表示を一つ選び、表示独立性から全基本退化との一致を得る。
規約：全正番号面の保存は後続ファイルで証明。使われ方：錐の後続段階の構成。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
open scoped _root_.Simplicial
variable {K X : SSet.{u}} {f : K ⟶ X} {N : ℕ}
variable (C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.TruncatedJoinConeData f N) (U : K _⦋N + 1⦌ → X _⦋N + 2⦌)

/-- 基本退化表示があれば標準錐、それ以外では指定された実充填を選ぶ。 -/
def truncatedConeNormalizeNext (σ : K _⦋N + 1⦌) : X _⦋N + 2⦌ := by
  classical
  exact if h : ∃ (i : Fin (N + 1)) (y : K _⦋N⦌), σ = K.σ i y then
    X.σ h.choose.succ (C.simplex N le_rfl h.choose_spec.choose)
  else U σ

/-- 正規化は全基本退化を同じ標準正番号退化へ厳密に写す。 -/
lemma truncatedConeNormalizeNext_degeneracy (i : Fin (N + 1)) (y : K _⦋N⦌) :
    truncatedConeNormalizeNext C U (K.σ i y) = X.σ i.succ (C.simplex N le_rfl y) := by
  classical
  unfold truncatedConeNormalizeNext
  split_ifs with h
  · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.truncatedConeDegeneracy_congr C h.choose i h.choose_spec.choose y
      h.choose_spec.choose_spec.symm
  · exact (h ⟨i, y, rfl⟩).elim

/-- 基本退化像の外では指定した実充填をそのまま保つ。 -/
lemma truncatedConeNormalizeNext_of_no_degeneracy (σ : K _⦋N + 1⦌)
    (h : ¬ ∃ (i : Fin (N + 1)) (y : K _⦋N⦌), σ = K.σ i y) :
    truncatedConeNormalizeNext C U σ = U σ := by
  classical
  simp only [truncatedConeNormalizeNext, dite_eq_right h]

/-- 非退化単体の実充填は変更されない。 -/
lemma truncatedConeNormalizeNext_of_nondegenerate (σ : K.nonDegenerate (N + 1)) :
    truncatedConeNormalizeNext C U σ.val = U σ.val := by
  apply truncatedConeNormalizeNext_of_no_degeneracy
  rintro ⟨i, y, hy⟩
  exact σ.prop (hy.symm ▸ K.σ_mem_degenerate i y)

/-- 標準退化錐の零面は同じ図式退化単体の像である。 -/
lemma truncatedConeDegeneracy_face_zero (i : Fin (N + 1)) (y : K _⦋N⦌) :
    X.δ 0 (X.σ i.succ (C.simplex N le_rfl y)) = f.app _ (K.σ i y) := by
  have h := X.δ_comp_σ_of_le_apply (i := (0 : Fin (N + 2)))
    (j := i) (Fin.zero_le _) (C.simplex N le_rfl y)
  simp only [Fin.castSucc_zero] at h
  exact h.trans ((congrArg (X.σ i) (C.face_zero N le_rfl y)).trans
    (SSet.σ_naturality_apply f i y).symm)

/-- 標準退化錐の始頂点は下次数錐の同じ apex。 -/
lemma truncatedConeDegeneracy_first_vertex (i : Fin (N + 1)) (y : K _⦋N⦌) :
    X.map (SimplexCategory.const ⦋0⦌ ⦋N + 2⦌ 0).op
      (X.σ i.succ (C.simplex N le_rfl y)) = C.apex := by
  have he : SimplexCategory.const ⦋0⦌ ⦋N + 2⦌ 0 ≫ SimplexCategory.σ i.succ =
      SimplexCategory.const ⦋0⦌ ⦋N + 1⦌ 0 := by
    apply SimplexCategory.Hom.ext_zero_left
    simp [SimplexCategory.σ]
  change X.map _ (X.map _ _) = _
  rw [← Functor.map_comp_apply, ← op_comp, he]
  exact C.first_vertex N le_rfl y

/-- 元の全充填の始頂点が同じなら、正規化後も同じ apex を保つ。 -/
lemma truncatedConeNormalizeNext_first_vertex
    (hU : ∀ σ, X.map (SimplexCategory.const ⦋0⦌ ⦋N + 2⦌ 0).op (U σ) = C.apex)
    (σ : K _⦋N + 1⦌) :
    X.map (SimplexCategory.const ⦋0⦌ ⦋N + 2⦌ 0).op
      (truncatedConeNormalizeNext C U σ) = C.apex := by
  classical
  unfold truncatedConeNormalizeNext
  split_ifs with h
  · exact truncatedConeDegeneracy_first_vertex C h.choose h.choose_spec.choose
  · exact hU σ

/-- 元の全充填の零面が指定どおりなら、正規化後も全零面を保つ。 -/
lemma truncatedConeNormalizeNext_face_zero
    (hU : ∀ σ, X.δ 0 (U σ) = f.app _ σ) (σ : K _⦋N + 1⦌) :
    X.δ 0 (truncatedConeNormalizeNext C U σ) = f.app _ σ := by
  classical
  unfold truncatedConeNormalizeNext
  split_ifs with h
  · exact (truncatedConeDegeneracy_face_zero C h.choose h.choose_spec.choose).trans
      (congrArg (f.app _) h.choose_spec.choose_spec.symm)
  · exact hU σ

end SerrePositivity.InfinityCategories.Project.DerivedCategories
