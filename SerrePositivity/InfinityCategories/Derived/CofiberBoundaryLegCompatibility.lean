module
public import SerrePositivity.InfinityCategories.Derived.CofiberBoundarySharedResiduals
public import SerrePositivity.InfinityCategories.Derived.SpanOnePrefixTransport
public import SerrePositivity.InfinityCategories.DGNerve.Checks

/-! # 標準 cofiber 境界の脚側の微分条件

概要：型付き残差の微分は標準包含・対角と後続右辺の合成に符号を掛けた式となる。
方針：生の Bianchi を対象・次数・各成分の異種等号に沿って移す。
規約：任意の非有界複体。使われ方：D7 の六成分線形系の脚側条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Opposite DifferentialGraded DGNerve CochainComplex HomComplex
open scoped Simplicial
variable {S : Type u} [CommRing S] {A B C : Complex S}

/-- 概要：r_B の微分は標準射との合成に (-1)^(n+1) を掛けた式。
方針：零未知データの脚側 Bianchi を標準 cofiber の Hom 座標へ移す。
規約：最初の頂点に標準余錐を指定する。使われ方：六成分線形系の整合条件。 -/
lemma cofiberBoundaryRhsB_differential {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g)) :
    δ (cofiberBoundaryDegree n + 1) (cofiberBoundaryDegree n + 1 + 1)
        (cofiberBoundaryRhsB f g b hb) =
      ((n : ℤ) + 1).negOnePow • (Cochain.ofHom (pushoutInclusionB f g)).comp
        (cofiberBoundaryRhs0 f g b hb) (zero_add (cofiberBoundaryDegree n + 1 + 1)) := by
  have H := SimplexData.span_onePrefix_differential_of_heq (A := S) (D := Complex S)
    (cofiberBoundaryLeftBase f g b)
    (spanBoundaryLeftData_equation (sliceUnderUncurry b) _)
    (spanBoundaryLeftZeroData_suffixHom (sliceUnderUncurry b))
    (spanSecondPrefix n) (spanSecondPrefix_lt_apex n)
    (cofiberCosliceBoundary_left_B f g b hb)
    (cofiberCosliceBoundary_left_apex f g b hb) rfl rfl
    (cofiberBoundaryRhs0 f g b hb) (cofiberBoundaryRhsB f g b hb)
    (Cochain.ofHom (pushoutInclusionB f g))
    (cofiberBoundaryRhs0_heq f g b hb).symm (cofiberBoundaryRhsB_heq f g b hb).symm
    (cofiberCosliceBoundary_left_inclusion_heq f g b hb)
  rw [Checks.complex_compose] at H
  exact H

/-- 概要：r_C の微分は標準射との合成に (-1)^(n+1) を掛けた式。
方針：零未知データの脚側 Bianchi を標準 cofiber の Hom 座標へ移す。
規約：最初の頂点に標準余錐を指定する。使われ方：六成分線形系の整合条件。 -/
lemma cofiberBoundaryRhsC_differential {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g)) :
    δ (cofiberBoundaryDegree n + 1) (cofiberBoundaryDegree n + 1 + 1)
        (cofiberBoundaryRhsC f g b hb) =
      ((n : ℤ) + 1).negOnePow • (Cochain.ofHom (pushoutInclusionC f g)).comp
        (cofiberBoundaryRhs0 f g b hb) (zero_add (cofiberBoundaryDegree n + 1 + 1)) := by
  have H := SimplexData.span_onePrefix_differential_of_heq (A := S) (D := Complex S)
    (cofiberBoundaryRightBase f g b)
    (spanBoundaryRightData_equation (sliceUnderUncurry b) _)
    (spanBoundaryRightZeroData_suffixHom (sliceUnderUncurry b))
    (spanSecondPrefix n) (spanSecondPrefix_lt_apex n)
    (cofiberCosliceBoundary_right_C f g b hb)
    (cofiberCosliceBoundary_right_apex f g b hb) (cofiberBoundaryTarget_right_eq f g b) rfl
    (cofiberBoundaryRhs0 f g b hb) (cofiberBoundaryRhsC f g b hb)
    (Cochain.ofHom (pushoutInclusionC f g))
    (cofiberBoundaryRhs0_heq_right f g b hb).symm (cofiberBoundaryRhsC_heq f g b hb).symm
    (cofiberCosliceBoundary_right_inclusion_heq f g b hb)
  rw [Checks.complex_compose] at H
  exact H

/-- 概要：r_A の微分は標準射との合成に (-1)^(n+1) を掛けた式。
方針：零未知データの脚側 Bianchi を標準 cofiber の Hom 座標へ移す。
規約：最初の頂点に標準余錐を指定する。使われ方：六成分線形系の整合条件。 -/
lemma cofiberBoundaryRhsA_differential {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g)) :
    δ (cofiberBoundaryDegree n + 1) (cofiberBoundaryDegree n + 1 + 1)
        (cofiberBoundaryRhsA f g b hb) =
      ((n : ℤ) + 1).negOnePow • (Cochain.ofHom (pushoutDiagonal f g)).comp
        (cofiberBoundaryRhs0 f g b hb) (zero_add (cofiberBoundaryDegree n + 1 + 1)) := by
  have H := SimplexData.span_onePrefix_differential_of_heq (A := S) (D := Complex S)
    (cofiberBoundaryLeftBase f g b)
    (spanBoundaryLeftData_equation (sliceUnderUncurry b) _)
    (spanBoundaryLeftZeroData_suffixHom (sliceUnderUncurry b))
    (0) (spanApex_pos n)
    (cofiberCosliceBoundary_left_A f g b hb)
    (cofiberCosliceBoundary_left_apex f g b hb) rfl rfl
    (cofiberBoundaryRhs0 f g b hb) (cofiberBoundaryRhsA f g b hb)
    (Cochain.ofHom (pushoutDiagonal f g))
    (cofiberBoundaryRhs0_heq f g b hb).symm (cofiberBoundaryRhsA_heq f g b hb).symm
    (cofiberCosliceBoundary_left_diagonal_heq f g b hb)
  rw [Checks.complex_compose] at H
  exact H

end SerrePositivity.InfinityCategories
