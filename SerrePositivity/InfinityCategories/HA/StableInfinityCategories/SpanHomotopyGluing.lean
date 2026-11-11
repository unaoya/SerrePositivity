module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.TerminalSpanComparison

/-! # 二本の枝のホモトピーの貼り合わせ

概要：始点で厳密に一致する二本の枝のホモトピーを span のホモトピーに貼る。
方針：標準ホーンの pushout を区間との積で送り、二つのホモトピーを貼る。
規約：枝への制限を厳密な等式で保持する。
使われ方：S4 の TR3 の span の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：ホモトピーの両端の表示を等号に沿って変える。
方針：両端の等式を合成し、ホモトピー自体は保持する。
規約：円柱上の射は厳密に同じ。使われ方：枝の制限の表示の照合。 -/
def stableHomotopyRetarget {A X : SSet.{u}} {f g f' g' : A ⟶ X}
    (H : SSet.Homotopy f g) (hf : f = f') (hg : g = g') : SSet.Homotopy f' g' where
  h := H.h
  h₀ := H.h₀.trans hf
  h₁ := H.h₁.trans hg
  rel := H.rel

/-- 概要：二つの枝の始点の道が一致すれば span のホモトピーとして貼れる。
方針：ホーンの pushout と区間の積の普遍性を使い、両端と制限を検査する。
規約：値域への追加仮定は不要。使われ方：TR3 の入力図式の比較。 -/
lemma exists_spanHomotopy_of_branchHomotopies {X : SSet.{u}}
    (F G : (horn 2 0 : SSet.{u}) ⟶ X)
    (L : SSet.Homotopy (horn₂₀.ι₀₁ ≫ F) (horn₂₀.ι₀₁ ≫ G))
    (R : SSet.Homotopy (horn₂₀.ι₀₂ ≫ F) (horn₂₀.ι₀₂ ≫ G))
    (h : (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u})) ≫ L.h =
      (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u})) ≫ R.h) :
    ∃ H : SSet.Homotopy F G,
      (horn₂₀.ι₀₁ ▷ (Δ[1] : SSet.{u})) ≫ H.h = L.h ∧
      (horn₂₀.ι₀₂ ▷ (Δ[1] : SSet.{u})) ≫ H.h = R.h := by
  have P : IsPushout (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u}))
      (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u}))
      (horn₂₀.ι₀₁ ▷ (Δ[1] : SSet.{u})) (horn₂₀.ι₀₂ ▷ (Δ[1] : SSet.{u})) :=
    horn₂₀.isPushout.map (tensorRight (Δ[1] : SSet.{u}))
  refine ⟨{
    h := P.desc L.h R.h h
    h₀ := ?_
    h₁ := ?_
    rel := ?_ }, P.inl_desc _ _ _, P.inr_desc _ _ _⟩
  · apply horn₂₀.isPushout.hom_ext
    · rw [← Category.assoc, ← SSet.ι₀_comp, Category.assoc, P.inl_desc, L.h₀]
      rfl
    · rw [← Category.assoc, ← SSet.ι₀_comp, Category.assoc, P.inr_desc, R.h₀]
      rfl
  · apply horn₂₀.isPushout.hom_ext
    · rw [← Category.assoc, ← SSet.ι₁_comp, Category.assoc, P.inl_desc, L.h₁]
      rfl
    · rw [← Category.assoc, ← SSet.ι₁_comp, Category.assoc, P.inr_desc, R.h₁]
      rfl
  · apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro z
    exact False.elim z.1.property

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
