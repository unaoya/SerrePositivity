module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.TruncatedConeDegeneracyFaces

/-! # 全面整合的な次次数充填からの切断錐の延長

概要：次次数の実充填を標準退化へ正規化し、切断錐を一段延長する。
方針：低い次数では元の単体族を保持し、新しい次数だけを追加する。
規約：入力の全充填の存在は別に供給する。使われ方：有限次数の実錐の帰納。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
open scoped _root_.Simplicial
variable {K X : SSet.{u}} {f : K ⟶ X} {N : ℕ}

/-- 次次数の全面・始頂点・退化整合性を持つ単体族を一段上の切断錐に束ねる。 -/
def TruncatedJoinConeData.successor (C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.TruncatedJoinConeData f N)
    (U : K _⦋N + 1⦌ → X _⦋N + 2⦌)
    (hzero : ∀ σ, X.δ 0 (U σ) = f.app _ σ)
    (hfirst : ∀ σ, X.map (SimplexCategory.const ⦋0⦌ ⦋N + 2⦌ 0).op (U σ) = C.apex)
    (hpositive : ∀ σ k, X.δ k.succ (U σ) = C.simplex N le_rfl (K.δ k σ))
    (hdegenerate : ∀ i y, U (K.σ i y) = X.σ i.succ (C.simplex N le_rfl y)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.TruncatedJoinConeData f (N + 1) := by
  classical
  let S (n : ℕ) (hn : n ≤ N + 1) (σ : K _⦋n⦌) : X _⦋n + 1⦌ :=
    if h : n ≤ N then C.simplex n h σ
    else by
      have he : n = N + 1 := by omega
      subst n
      exact U σ
  have low (n : ℕ) (hn : n ≤ N) (σ : K _⦋n⦌) :
      S n (by omega) σ = C.simplex n hn σ := by simp only [S, dite_eq_left hn]
  have top (σ : K _⦋N + 1⦌) : S (N + 1) le_rfl σ = U σ := by
    simp only [S, dite_eq_right (show ¬ N + 1 ≤ N by omega)]
  refine {
    apex := C.apex
    simplex := S
    face_zero := ?_
    first_vertex := ?_
    face_positive := ?_
    degeneracy_positive := ?_ }
  · intro n hn σ
    by_cases h : n ≤ N
    · rw [low n h]
      exact C.face_zero n h σ
    · have he : n = N + 1 := by omega
      subst n
      rw [top]
      exact hzero σ
  · intro n hn σ
    by_cases h : n ≤ N
    · rw [low n h]
      exact C.first_vertex n h σ
    · have he : n = N + 1 := by omega
      subst n
      rw [top]
      exact hfirst σ
  · intro n hn σ i
    by_cases h : n + 1 ≤ N
    · rw [low (n + 1) h, low n (by omega)]
      exact C.face_positive n h σ i
    · have he : n = N := by omega
      subst n
      rw [top, low N le_rfl]
      exact hpositive σ i
  · intro n hn σ i
    by_cases h : n + 1 ≤ N
    · rw [low (n + 1) h, low n (by omega)]
      exact C.degeneracy_positive n h σ i
    · have he : n = N := by omega
      subst n
      rw [top, low N le_rfl]
      exact (hdegenerate i σ).symm

/-- 全面・始頂点を満たす任意の次次数充填は、標準退化へ直して一段延長できる。 -/
def TruncatedJoinConeData.normalizedSuccessor (C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.TruncatedJoinConeData f N)
    (U : K _⦋N + 1⦌ → X _⦋N + 2⦌)
    (hzero : ∀ σ, X.δ 0 (U σ) = f.app _ σ)
    (hfirst : ∀ σ, X.map (SimplexCategory.const ⦋0⦌ ⦋N + 2⦌ 0).op (U σ) = C.apex)
    (hpositive : ∀ σ k, X.δ k.succ (U σ) = C.simplex N le_rfl (K.δ k σ)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.TruncatedJoinConeData f (N + 1) :=
  C.successor (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.truncatedConeNormalizeNext C U)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.truncatedConeNormalizeNext_face_zero C U hzero)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.truncatedConeNormalizeNext_first_vertex C U hfirst)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.truncatedConeNormalizeNext_face_positive C U hpositive)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.truncatedConeNormalizeNext_degeneracy C U)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
