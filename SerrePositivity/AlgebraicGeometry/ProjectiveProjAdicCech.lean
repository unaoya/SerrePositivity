module

public import SerrePositivity.AlgebraicGeometry.SchemeAdicBaseChange
public import SerrePositivity.AlgebraicGeometry.SchemeStructureCechPullbackComposition
public import SerrePositivity.AlgebraicGeometry.ReesAdicNativeClosedCech

/-!
概要：Proj の実際の I 進閉厚化の Čech 複体と、その間の実際の引き戻しを定義する。
方針：canonical な pullback と、構造層の細分付き引き戻しを用いる。
規約：Rees の比較から遷移を定義せず、実際のスキームの射から定義する。
使われ方：形式関数の互換族と、I 進遷移への自然性の接続。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
variable {R S : Type u} {ι : Type} [CommRing R] [CommRing S]
variable [LinearOrder ι] [Fintype ι]
variable [Algebra R S] [Algebra (MvPolynomial ι R) S]
variable [IsScalarTower R (MvPolynomial ι R) S]
variable (I : Ideal R) (G : ℕ → Submodule R S) [GradedRing G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]

/-- Proj の指定した大域スカラーに沿う実際の I 進閉厚化。 -/
abbrev projectiveProjAdicScheme (n : ℕ) :=
  schemeAdicBaseChange I (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G)) n

/-- Proj の実際の閉厚化からの射。 -/
abbrev projectiveProjAdicProjection (n : ℕ) :=
  schemeAdicBaseChangeProjection I (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G)) n

/-- 実際の I 進閉厚化の逆像被覆の構造層の Čech 複体。 -/
abbrev projectiveProjAdicCechComplex (n : ℕ) :=
  fullCechComplex (openCoverCechDiagram
    (projectiveProjPullbackCechPresheaf G (projectiveProjAdicProjection I G n))
    (fun i ↦ projectiveProjAdicProjection I G n ⁻¹ᵁ projectiveProjCechOpen (ι := ι) G i))

/-- Rees の商の Čech 複体と canonical な実際の閉厚化の Čech 複体の同型。 -/
def projectiveProjAdicCechComplexIso (n : ℕ) :
    (reesAdicProjectiveClosedCechShortComplex (ι := ι) I G n 0).X₃ ≅
      projectiveProjAdicCechComplex (ι := ι) I G n :=
  reesAdicNativeClosedCechComplexIso (ι := ι) I G n
    (schemeAdicBaseChangeStructure I
      (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G)) n)
    (projectiveProjAdicProjection I G n)
    (schemeAdicBaseChange_isPullback I
      (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G)) n)

/-- 実際の厚化間のスキームの射が誘導する Čech の遷移。 -/
def projectiveProjAdicCechTransition (i j : ℕ) (h : j ≤ i) :
    projectiveProjAdicCechComplex (ι := ι) I G i ⟶ projectiveProjAdicCechComplex (ι := ι) I G j :=
  schemeStructureCechRefinedPullbackMap
    (schemeAdicBaseChangeTransition I
      (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G)) i j h)
    ((projectiveProjAdicProjection I G i).appTop.hom.comp (projectiveScalarToGlobalSections G))
    ((projectiveProjAdicProjection I G j).appTop.hom.comp (projectiveScalarToGlobalSections G))
    (schemeStructureCechPullbackScalar_comp (projectiveProjAdicProjection I G i)
      (schemeAdicBaseChangeTransition I
        (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G)) i j h)
      (projectiveProjAdicProjection I G j)
      (schemeAdicBaseChangeTransition_projection I _ i j h) (projectiveScalarToGlobalSections G))
    (fun l ↦ projectiveProjAdicProjection I G i ⁻¹ᵁ projectiveProjCechOpen (ι := ι) G l)
    (fun l ↦ projectiveProjAdicProjection I G j ⁻¹ᵁ projectiveProjCechOpen (ι := ι) G l) id
    (schemeStructureCechPreimage_refinement (projectiveProjAdicProjection I G i)
      (schemeAdicBaseChangeTransition I
        (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G)) i j h)
      (projectiveProjAdicProjection I G j) (schemeAdicBaseChangeTransition_projection I _ i j h)
      (projectiveProjCechOpen (ι := ι) G))

end SerrePositivity.AlgebraicGeometry
