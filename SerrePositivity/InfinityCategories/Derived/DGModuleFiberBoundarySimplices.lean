module
public import SerrePositivity.InfinityCategories.Derived.DGModuleFiberBoundaryTriangleEquations

/-! # 標準 fiber の境界を満たす左右の単体

概要：明示解を挿入した左右の候補は全ての単体方程式を満たす。
方針：先頭集合を含まない集合は既知方程式、含む集合は四分類で検証済みの未知方程式へ戻す。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：二つの標準セルの貼合せへの入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories

open CategoryTheory Opposite DifferentialGraded DGNerve
open scoped Simplicial

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {M N : ModuleCategory A D}

/-- 概要：Left 側候補は全ての有限部分集合で単体の方程式を満たす。
方針：既知集合と四種類の未知集合を分け、それぞれの検証済み方程式を使う。
規約：HA Proposition 1.3.1.10。使われ方：候補を実際の dg nerve の単体にする。 -/
lemma dgModuleFiberBoundaryLeftCandidate_all_equations {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceOver (pullbackCospan (dgModuleFiberSquare A D f)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (dgModuleFiberCone A D f))
    (I : Finset (Fin (n + 4))) : (dgModuleFiberBoundaryLeftCandidate A D f b hb).Equation I := by
  by_cases hprefix : cospanPrefixFaces n ⊆ I
  · rcases cospanUnknown_cases I hprefix with h0 | hB | hD | hfull
    · subst I
      exact dgModuleFiberBoundaryLeftCandidate_prefix_equation A D f b hb
    · subst I
      exact dgModuleFiberBoundaryLeftCandidate_first_equation A D f b hb
    · subst I
      exact dgModuleFiberBoundaryLeftCandidate_last_equation A D f b hb
    · rw [cospanPrefix_insert_both] at hfull
      subst I
      exact dgModuleFiberBoundaryLeftCandidate_full_equation A D f b hb
  · exact dgModuleFiberBoundaryLeftCandidate_equation A D f b hb I hprefix

/-- 概要：Left 側の明示解を挿入した候補から dg nerve の実際の単体を作る。
方針：全ての集合で検証した方程式を候補データに付ける。
規約：HA Proposition 1.3.1.10。使われ方：標準 join の左右のセルに与える単体。 -/
def dgModuleFiberBoundaryLeftSimplex {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceOver (pullbackCospan (dgModuleFiberSquare A D f)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (dgModuleFiberCone A D f)) : Simplex A (RightModule A D) (n + 3) where
  toSimplexData := dgModuleFiberBoundaryLeftCandidate A D f b hb
  equation := dgModuleFiberBoundaryLeftCandidate_all_equations A D f b hb

/-- 概要：Left 側単体の underlying data は構成した候補データ。
方針：定義を評価する。
規約：HA Construction 1.3.1.6。使われ方：候補の面や成分の保存定理を単体へ適用する。 -/
lemma dgModuleFiberBoundaryLeftSimplex_toData {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceOver (pullbackCospan (dgModuleFiberSquare A D f)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (dgModuleFiberCone A D f)) :
    (dgModuleFiberBoundaryLeftSimplex A D f b hb).toSimplexData =
      dgModuleFiberBoundaryLeftCandidate A D f b hb := rfl

/-- 概要：Right 側候補は全ての有限部分集合で単体の方程式を満たす。
方針：既知集合と四種類の未知集合を分け、それぞれの検証済み方程式を使う。
規約：HA Proposition 1.3.1.10。使われ方：候補を実際の dg nerve の単体にする。 -/
lemma dgModuleFiberBoundaryRightCandidate_all_equations {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceOver (pullbackCospan (dgModuleFiberSquare A D f)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (dgModuleFiberCone A D f))
    (I : Finset (Fin (n + 4))) : (dgModuleFiberBoundaryRightCandidate A D f b hb).Equation I := by
  by_cases hprefix : cospanPrefixFaces n ⊆ I
  · rcases cospanUnknown_cases I hprefix with h0 | hB | hD | hfull
    · subst I
      exact dgModuleFiberBoundaryRightCandidate_prefix_equation A D f b hb
    · subst I
      exact dgModuleFiberBoundaryRightCandidate_first_equation A D f b hb
    · subst I
      exact dgModuleFiberBoundaryRightCandidate_last_equation A D f b hb
    · rw [cospanPrefix_insert_both] at hfull
      subst I
      exact dgModuleFiberBoundaryRightCandidate_full_equation A D f b hb
  · exact dgModuleFiberBoundaryRightCandidate_equation A D f b hb I hprefix

/-- 概要：Right 側の明示解を挿入した候補から dg nerve の実際の単体を作る。
方針：全ての集合で検証した方程式を候補データに付ける。
規約：HA Proposition 1.3.1.10。使われ方：標準 join の左右のセルに与える単体。 -/
def dgModuleFiberBoundaryRightSimplex {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceOver (pullbackCospan (dgModuleFiberSquare A D f)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (dgModuleFiberCone A D f)) : Simplex A (RightModule A D) (n + 3) where
  toSimplexData := dgModuleFiberBoundaryRightCandidate A D f b hb
  equation := dgModuleFiberBoundaryRightCandidate_all_equations A D f b hb

/-- 概要：Right 側単体の underlying data は構成した候補データ。
方針：定義を評価する。
規約：HA Construction 1.3.1.6。使われ方：候補の面や成分の保存定理を単体へ適用する。 -/
lemma dgModuleFiberBoundaryRightSimplex_toData {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceOver (pullbackCospan (dgModuleFiberSquare A D f)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (dgModuleFiberCone A D f)) :
    (dgModuleFiberBoundaryRightSimplex A D f b hb).toSimplexData =
      dgModuleFiberBoundaryRightCandidate A D f b hb := rfl

end SerrePositivity.InfinityCategories
