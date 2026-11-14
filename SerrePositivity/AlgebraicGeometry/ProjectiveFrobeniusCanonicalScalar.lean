module

public import SerrePositivity.AlgebraicGeometry.ProjectiveFrobeniusCanonicalDiagram
public import SerrePositivity.AlgebraicGeometry.ProjectivePerfCechScalarAugmentation

/-!
概要：F8 のスカラー増大写像を、実際の環の係数図式のスカラーの自然変換と同定する。
方針：各標準開への代数写像のスカラーとの可換性と定義を評価する。
規約：H⁰ 比較をスカラーの自然性の仮定にしない。
使われ方：共通細分・底変換等の環の切断の射に沿う増大写像の自然性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
variable {R A : Type u} {ι : Type} [CommRing R] [CommRing A]
variable [LinearOrder ι] [Fintype ι]
variable [Algebra R A] [Algebra (MvPolynomial ι R) A]
variable [IsScalarTower R (MvPolynomial ι R) A]
variable (G : ℕ → Submodule R A) [GradedRing G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hA : (p : A) = 0)

/-- 基底環の定数図式から標準開の実際の切断の環図式へのスカラーの自然変換。 -/
def projectiveHomogeneousChartScalarNatTrans :
    (Functor.const (Finset ι)).obj (CommRingCat.of R) ⟶
      algebraCechRingDiagram (projectiveHomogeneousChartAlgebraDiagram (ι := ι) G) where
  app T := CommRingCat.ofHom
    (algebraMap R ((projectiveHomogeneousChartAlgebraDiagram (ι := ι) G).obj T))
  naturality {T U} f := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    exact (((projectiveHomogeneousChartAlgebraDiagram (ι := ι) G).map f).hom.commutes r).symm

/-- 係数図式の canonical な比較を介しても、スカラーの増大写像は同じ環の射。 -/
theorem projectivePerfCechScalarAugmentation_canonical
    (a : FrobeniusDirectLimit R p hp hR) (t : Fin 1 → ι) :
    ((projectiveFrobeniusRingChartDiagram_isoCanonical (ι := ι) G p hp hR hA).hom.app
      (cechTupleSupport t)).hom
      (projectivePerfCechScalarAugmentation (ι := ι) G p hp hR hA a t) =
    ((frobeniusRingDiagramMap p hp (fun _ ↦ hR)
      (hE := fun T ↦ projectiveHomogeneousChart_primeCast G p hR T)
      (projectiveHomogeneousChartScalarNatTrans (ι := ι) G)).app (cechTupleSupport t)).hom a := rfl

end SerrePositivity.AlgebraicGeometry
