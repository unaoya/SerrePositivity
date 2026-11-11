module

public import SerrePositivity.AlgebraicGeometry.ProjectiveHomogeneousChartRestriction

/-!
概要：有限性を計算したチャートの各項と制限を、Proj の構造層の切断に対応させる。
方針：次数零局所化の標準開同型と、その制限との自然性を使う。
規約：非空の有限交叉を扱う。被覆には irrelevant ideal の生成条件を指定する。
使われ方：射影的な場合の構造層の Čech 計算。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.AlgebraicGeometry

open _root_.AlgebraicGeometry CategoryTheory

universe u v

variable {R : Type u} {ι : Type v} {S : Type (max u v)}
variable [CommRing R] [CommRing S] [LinearOrder ι] [Fintype ι]
variable [Algebra R S] [Algebra (MvPolynomial ι R) S]
variable [IsScalarTower R (MvPolynomial ι R) S]
variable (G : ℕ → Submodule R S) [GradedRing G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]

/-- 変数の像の積に対応する標準開は、各変数の像の標準開の有限交叉。 -/
theorem projectiveProjStandardOpen_eq_intersection (T : Finset ι) :
    Proj.basicOpen G (algebraMap (MvPolynomial ι R) S (projectiveLaurentDenominator R T)) =
      T.inf (fun i ↦ Proj.basicOpen G (algebraMap (MvPolynomial ι R) S (MvPolynomial.X i))) := by
  rw [projectivePolynomialDenominatorImage]
  exact proj_basicOpen_finset_prod G _ T

/-- Čech の非空有限交叉の係数環と、その上の構造層の切断の環同型。 -/
def projectiveProjStandardSectionIso (T : Finset ι) (hT : T.Nonempty) :
    CommRingCat.of (HomogeneousLocalization.Away G
        (algebraMap (MvPolynomial ι R) S (projectiveLaurentDenominator R T))) ≅
      Γ(Proj G, Proj.basicOpen G
        (algebraMap (MvPolynomial ι R) S (projectiveLaurentDenominator R T))) :=
  Proj.basicOpenIsoAway G _ (projectivePolynomialDenominatorImage_mem G T)
    (Finset.card_pos.mpr hT)

/-- 添字を増やすときの分母の像を、追加した変数の像で因数分解する。 -/
theorem projectivePolynomialDenominatorImage_factor {T U : Finset ι} (h : T ⊆ U) :
    algebraMap (MvPolynomial ι R) S (projectiveLaurentDenominator R U) =
      algebraMap (MvPolynomial ι R) S (projectiveLaurentDenominator R T) *
        algebraMap (MvPolynomial ι R) S (projectiveLaurentDenominator R (U \ T)) := by
  rw [← map_mul, projectiveLaurentDenominator_sdiff R h]

/-- 有限性を計算した係数の制限は、標準開上の構造層の切断の制限に対応する。 -/
theorem projectiveProjStandardSectionIso_naturality
    {T U : Finset ι} (hT : T.Nonempty) (h : T ⊆ U)
    (z : (projectiveHomogeneousChartDiagram (ι := ι) G).obj T) :
    (projectiveProjStandardSectionIso G U (Finset.Nonempty.mono h hT)).hom.hom
        (((projectiveHomogeneousChartDiagram (ι := ι) G).map (homOfLE h)).hom z) =
      ((Proj G).presheaf.map (homOfLE (Proj.basicOpen_mono G _ _
        ⟨_, projectivePolynomialDenominatorImage_factor (R := R) (S := S) h⟩)).op).hom
        ((projectiveProjStandardSectionIso G T hT).hom.hom z) := by
  rw [projectiveHomogeneousChartDiagram_map]
  exact congrArg
    (fun f : CommRingCat.of (HomogeneousLocalization.Away G
        (algebraMap (MvPolynomial ι R) S (projectiveLaurentDenominator R T))) ⟶
          Γ(Proj G, Proj.basicOpen G
            (algebraMap (MvPolynomial ι R) S (projectiveLaurentDenominator R U))) ↦ f.hom z)
    (Proj.awayMap_awayToSection G (projectivePolynomialDenominatorImage_mem G (U \ T))
      (projectivePolynomialDenominatorImage_factor (R := R) (S := S) h))

/-- 次数一の変数の像が irrelevant ideal を生成する場合の標準アフィン開被覆。 -/
def projectiveProjStandardAffineOpenCover
    (hspan : (HomogeneousIdeal.irrelevant G).toIdeal ≤ Ideal.span
      (Set.range (fun i : ι ↦ algebraMap (MvPolynomial ι R) S (MvPolynomial.X i)))) :
    (Proj G).AffineOpenCover :=
  projStandardAffineOpenCover G _ (projectivePolynomialVariableImage_mem G) hspan

end SerrePositivity.AlgebraicGeometry
