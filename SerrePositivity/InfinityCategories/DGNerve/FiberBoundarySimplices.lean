module
public import SerrePositivity.InfinityCategories.DGNerve.FiberBoundaryTriangleEquations

/-! # 標準 fiber の境界を満たす左右の単体

概要：明示解を挿入した左右の候補は全ての単体方程式を満たす。
方針：先頭集合を含まない集合は既知方程式、含む集合は四分類で検証済みの未知方程式へ戻す。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：二つの標準セルの貼合せへの入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.InfinityCategories.DGNerve

open CategoryTheory Opposite DifferentialGraded CochainComplex HomComplex
open scoped Simplicial

variable {A : Type u} [CommRing A] {B C D : Complex A}

/-- 概要：Left 側候補は全ての有限部分集合で単体の方程式を満たす。
方針：既知集合と四種類の未知集合を分け、それぞれの検証済み方程式を使う。
規約：HA Proposition 1.3.1.10。使われ方：候補を実際の dg nerve の単体にする。 -/
lemma fiberBoundaryLeftCandidate_all_equations {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h))
    (I : Finset (Fin (n + 4))) : (fiberBoundaryLeftCandidate g h b hb).Equation I := by
  by_cases hprefix : cospanPrefixFaces n ⊆ I
  · rcases cospanUnknown_cases I hprefix with h0 | hB | hD | hfull
    · subst I
      exact fiberBoundaryLeftCandidate_prefix_equation g h b hb
    · subst I
      exact fiberBoundaryLeftCandidate_first_equation g h b hb
    · subst I
      exact fiberBoundaryLeftCandidate_last_equation g h b hb
    · rw [cospanPrefix_insert_both] at hfull
      subst I
      exact fiberBoundaryLeftCandidate_full_equation g h b hb
  · exact fiberBoundaryLeftCandidate_equation g h b hb I hprefix

/-- 概要：Left 側の明示解を挿入した候補から dg nerve の実際の単体を作る。
方針：全ての集合で検証した方程式を候補データに付ける。
規約：HA Proposition 1.3.1.10。使われ方：標準 join の左右のセルに与える単体。 -/
def fiberBoundaryLeftSimplex {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h)) : Simplex A (Complex A) (n + 3) where
  toSimplexData := fiberBoundaryLeftCandidate g h b hb
  equation := fiberBoundaryLeftCandidate_all_equations g h b hb

/-- 概要：Left 側単体の underlying data は構成した候補データ。
方針：定義を評価する。
規約：HA Construction 1.3.1.6。使われ方：候補の面や成分の保存定理を単体へ適用する。 -/
lemma fiberBoundaryLeftSimplex_toData {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h)) :
    (fiberBoundaryLeftSimplex g h b hb).toSimplexData = fiberBoundaryLeftCandidate g h b hb := rfl

/-- 概要：Right 側候補は全ての有限部分集合で単体の方程式を満たす。
方針：既知集合と四種類の未知集合を分け、それぞれの検証済み方程式を使う。
規約：HA Proposition 1.3.1.10。使われ方：候補を実際の dg nerve の単体にする。 -/
lemma fiberBoundaryRightCandidate_all_equations {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h))
    (I : Finset (Fin (n + 4))) : (fiberBoundaryRightCandidate g h b hb).Equation I := by
  by_cases hprefix : cospanPrefixFaces n ⊆ I
  · rcases cospanUnknown_cases I hprefix with h0 | hB | hD | hfull
    · subst I
      exact fiberBoundaryRightCandidate_prefix_equation g h b hb
    · subst I
      exact fiberBoundaryRightCandidate_first_equation g h b hb
    · subst I
      exact fiberBoundaryRightCandidate_last_equation g h b hb
    · rw [cospanPrefix_insert_both] at hfull
      subst I
      exact fiberBoundaryRightCandidate_full_equation g h b hb
  · exact fiberBoundaryRightCandidate_equation g h b hb I hprefix

/-- 概要：Right 側の明示解を挿入した候補から dg nerve の実際の単体を作る。
方針：全ての集合で検証した方程式を候補データに付ける。
規約：HA Proposition 1.3.1.10。使われ方：標準 join の左右のセルに与える単体。 -/
def fiberBoundaryRightSimplex {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h)) : Simplex A (Complex A) (n + 3) where
  toSimplexData := fiberBoundaryRightCandidate g h b hb
  equation := fiberBoundaryRightCandidate_all_equations g h b hb

/-- 概要：Right 側単体の underlying data は構成した候補データ。
方針：定義を評価する。
規約：HA Construction 1.3.1.6。使われ方：候補の面や成分の保存定理を単体へ適用する。 -/
lemma fiberBoundaryRightSimplex_toData {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h)) :
    (fiberBoundaryRightSimplex g h b hb).toSimplexData = fiberBoundaryRightCandidate g h b hb := rfl

end SerrePositivity.InfinityCategories.DGNerve
