module

public import SerrePositivity.AlgebraicGeometry.ProjectiveProjAdicCech
public import SerrePositivity.AlgebraicGeometry.ReesAdicNativeClosedProjection
public import SerrePositivity.AlgebraicGeometry.ReesClosedCechTransition

/-!
概要：実際の I 進 Čech 遷移と Rees の遷移を、同じ射影から自然に比較する。
方針：元の係数からの全射を合成して比較し、実際の引き戻しの合成を用いる。
規約：遷移は実際の厚化のスキームの射から定義したものを使う。
使われ方：Čech 版の形式関数の互換族と I 進自然性。
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

/-- 元の Proj の構造層の Čech 複体から、実際の閉厚化への引き戻し。 -/
def projectiveProjAdicCechProjection (n : ℕ) :
    fullCechComplex (openCoverCechDiagram (schemeStructureCechPresheaf (Proj G) ⋙
      ModuleCat.restrictScalars (projectiveScalarToGlobalSections G))
        (projectiveProjCechOpen (ι := ι) G)) ⟶ projectiveProjAdicCechComplex (ι := ι) I G n :=
  schemeStructureCechRefinedPullbackMap (projectiveProjAdicProjection I G n)
    (projectiveScalarToGlobalSections G)
    ((projectiveProjAdicProjection I G n).appTop.hom.comp (projectiveScalarToGlobalSections G)) rfl
    (projectiveProjCechOpen (ι := ι) G)
    (fun i ↦ projectiveProjAdicProjection I G n ⁻¹ᵁ projectiveProjCechOpen (ι := ι) G i)
    id (fun _ ↦ le_rfl)

/-- 実際の閉厚化への射影は、厚化間の実際の Čech 遷移と可換。 -/
theorem projectiveProjAdicCechProjection_transition (i j : ℕ) (h : j ≤ i) :
    projectiveProjAdicCechProjection (ι := ι) I G i ≫
        projectiveProjAdicCechTransition (ι := ι) I G i j h =
      projectiveProjAdicCechProjection (ι := ι) I G j :=
  schemeStructureCechRefinedPullbackMap_comp (projectiveProjAdicProjection I G i)
    (schemeAdicBaseChangeTransition I
      (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G)) i j h)
    (projectiveProjAdicProjection I G j)
    (schemeAdicBaseChangeTransition_projection I
      (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G)) i j h)
    (projectiveScalarToGlobalSections G)
    ((projectiveProjAdicProjection I G i).appTop.hom.comp (projectiveScalarToGlobalSections G))
    ((projectiveProjAdicProjection I G j).appTop.hom.comp (projectiveScalarToGlobalSections G)) rfl
    (schemeStructureCechPullbackScalar_comp (projectiveProjAdicProjection I G i)
      (schemeAdicBaseChangeTransition I
        (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G)) i j h)
      (projectiveProjAdicProjection I G j)
      (schemeAdicBaseChangeTransition_projection I
        (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G)) i j h)
      (projectiveScalarToGlobalSections G)) rfl
    (projectiveProjCechOpen (ι := ι) G)
    (fun l ↦ projectiveProjAdicProjection I G i ⁻¹ᵁ projectiveProjCechOpen (ι := ι) G l)
    (fun l ↦ projectiveProjAdicProjection I G j ⁻¹ᵁ projectiveProjCechOpen (ι := ι) G l)
    (fun _ ↦ le_rfl)
    (schemeStructureCechPreimage_refinement (projectiveProjAdicProjection I G i)
      (schemeAdicBaseChangeTransition I
        (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G)) i j h)
      (projectiveProjAdicProjection I G j)
      (schemeAdicBaseChangeTransition_projection I
        (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G)) i j h)
      (projectiveProjCechOpen (ι := ι) G)) (fun _ ↦ le_rfl)

/-- Rees の射影を実際の閉厚化へ移す複体の比較は、元の射影と可換。 -/
theorem projectiveProjAdicCechComplexIso_projection (n : ℕ) :
    (reesAdicProjectiveClosedCechShortComplex (ι := ι) I G n 0).g ≫
        (projectiveProjAdicCechComplexIso (ι := ι) I G n).hom =
      (projectiveProjNativeNatCechComplexIso (ι := ι) G).hom ≫
        projectiveProjAdicCechProjection (ι := ι) I G n :=
  reesAdicNativeClosedCechComplexIso_projection_refined (ι := ι) I G n
    (schemeAdicBaseChangeStructure I
      (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G)) n)
    (projectiveProjAdicProjection I G n)
    (schemeAdicBaseChange_isPullback I
      (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G)) n)

/-- Rees の商と実際の閉厚化の Čech 複体の比較は、I 進遷移に自然。 -/
theorem projectiveProjAdicCechComplexIso_transition (i j : ℕ) (h : j ≤ i) :
    (reesAdicProjectiveClosedCechShortComplexMap (ι := ι) I G i j h 0).τ₃ ≫
        (projectiveProjAdicCechComplexIso (ι := ι) I G j).hom =
      (projectiveProjAdicCechComplexIso (ι := ι) I G i).hom ≫
        projectiveProjAdicCechTransition (ι := ι) I G i j h := by
  let qi := (reesAdicProjectiveClosedCechShortComplex (ι := ι) I G i 0).g
  let qj := (reesAdicProjectiveClosedCechShortComplex (ι := ι) I G j 0).g
  let τ := (reesAdicProjectiveClosedCechShortComplexMap (ι := ι) I G i j h 0).τ₃
  let ei := projectiveProjAdicCechComplexIso (ι := ι) I G i
  let ej := projectiveProjAdicCechComplexIso (ι := ι) I G j
  let s := projectiveProjNativeNatCechComplexIso (ι := ι) G
  let pi := projectiveProjAdicCechProjection (ι := ι) I G i
  let pj := projectiveProjAdicCechProjection (ι := ι) I G j
  let t := projectiveProjAdicCechTransition (ι := ι) I G i j h
  haveI : Epi qi := (reesAdicProjectiveClosedCechShortComplex_shortExact (ι := ι) I G i 0).epi_g
  have hq : qi ≫ τ = qj := by
    have hc : 𝟙 _ ≫ qj = qi ≫ τ :=
      (reesAdicProjectiveClosedCechShortComplexMap (ι := ι) I G i j h 0).comm₂₃
    simpa only [Category.id_comp] using hc.symm
  have hi : qi ≫ ei.hom = s.hom ≫ pi := projectiveProjAdicCechComplexIso_projection I G i
  have hj : qj ≫ ej.hom = s.hom ≫ pj := projectiveProjAdicCechComplexIso_projection I G j
  have ht : pi ≫ t = pj := projectiveProjAdicCechProjection_transition I G i j h
  apply (cancel_epi qi).mp
  change qi ≫ (τ ≫ ej.hom) = qi ≫ (ei.hom ≫ t)
  calc
    _ = qj ≫ ej.hom := by rw [← Category.assoc, hq]
    _ = s.hom ≫ pj := hj
    _ = s.hom ≫ (pi ≫ t) := congrArg (fun f ↦ s.hom ≫ f) ht.symm
    _ = _ := by rw [← Category.assoc, ← hi, Category.assoc]

end SerrePositivity.AlgebraicGeometry
