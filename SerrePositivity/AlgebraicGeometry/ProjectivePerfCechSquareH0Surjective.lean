module

public import SerrePositivity.AlgebraicGeometry.ProjectivePerfCechSquareLowDegree

/-!
概要：F7 の全射性を、実際の四角形の差の余鎖写像の H⁰ の全射性へ移す。
方針：閉厚化側のコサイクルを H⁰ へ戻して持ち上げ、cyclesMap を全射にする。
規約：Mathlib の H と実際の余鎖写像について述べる。
使われ方：F8 の増大全複体の Acyclic 判定の H⁰ の入力。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
universe u v
variable {R A : Type u} {ι : Type} [CommRing R] [CommRing A]
variable [LinearOrder ι] [Fintype ι]
variable [Algebra R A] [Algebra (MvPolynomial ι R) A]
variable [IsScalarTower R (MvPolynomial ι R) A]
variable (G : ℕ → Submodule R A) [GradedRing G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
variable (I : Ideal R) (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hA : (p : A) = 0)
local instance perfCechSquareH0SurjectiveGradedRing (n : ℕ) :
    GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) :=
  reesClosedRingGradedRing I G n

variable [IsNoetherianRing R] [Module.Finite (MvPolynomial ι R) A]
variable (hspan : (HomogeneousIdeal.irrelevant G).toIdeal ≤ Ideal.span
  (Set.range (fun i : ι ↦ algebraMap (MvPolynomial ι R) A (MvPolynomial.X i))))
variable [IsIso (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G) ∣_
  affineCenterComplement I)]
variable [Surjective (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G))]

include hspan in
/-- F7 の全射性は、実際の差の余鎖写像の H⁰ の全射性を与える。 -/
theorem projectivePerfCechSquareDifferenceMap_homology_zero_surjective :
    Function.Surjective (ShortComplex.homologyMap
      ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} ℤ) (.up ℕ) 0 0 1).map
        (projectivePerfCechSquareDifferenceMap (ι := ι) G I p hp hR hA))).hom := by
  let E := projectiveFrobeniusRingChartDiagram (ι := ι)
    (projectiveRingQuotientGrade ((I ^ 1).map (algebraMap R A)) G) p hp hR
    (frobeniusQuotientPrimeCast p hA ((I ^ 1).map (algebraMap R A)))
  let C := projectivePerfCechSquareSource (ι := ι) G I p hp hR hA
  let g := projectivePerfCechSquareDifferenceMap (ι := ι) G I p hp hR hA
  let S := C.sc' 0 0 1
  let T := (fullCechComplex E).sc' 0 0 1
  let φ := (HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} ℤ) (.up ℕ) 0 0 1).map g
  change Function.Surjective (ShortComplex.homologyMap φ).hom
  apply (ModuleCat.epi_iff_surjective _).mp
  apply ShortComplex.epi_homologyMap_of_epi_cyclesMap' φ
  apply (ModuleCat.epi_iff_surjective _).mpr
  intro z
  let y := T.iCycles.hom z
  have hy0 : T.g.hom y = 0 := by
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] using congrArg (fun m ↦ m.hom z) T.iCycles_g
  have hy : fullCechDifferential E 1 y = 0 := by
    change ((fullCechComplex E).d 0 1).hom y = 0 at hy0
    rw [fullCechComplex_d] at hy0
    exact hy0
  let h : (fullCechComplex E).homology 0 := (fullCechH0KernelIso E).inv.hom ⟨y, hy⟩
  obtain ⟨b, hb⟩ := (projectivePerfCechH0_square_exact (ι := ι) G I p hp hR hA hspan).2.2 h
  let x := projectivePerfCechH0ToSquareCochains (ι := ι) G I p hp hR hA b
  have hx : S.g.hom x = 0 := fullCechH0ZeroTermCochainMap_cycle
    (projectiveFrobeniusRingChartDiagram (ι := ι) G p hp hR hA)
    (ModuleCat.of ℤ (FrobeniusDirectLimit (R ⧸ (I ^ 1)) p hp
      (frobeniusQuotientPrimeCast p hR (I ^ 1)))) b
  have hd : (g.f 0).hom x = y :=
    (projectivePerfCechH0Difference_kernel (ι := ι) G I p hp hR hA b.1 b.2).symm.trans
      ((congrArg (fun k ↦ ((fullCechH0KernelIso E).hom.hom k).val) hb).trans
        (congrArg (fun k ↦ k.val) ((fullCechH0KernelIso E).toLinearEquiv.apply_symm_apply ⟨y, hy⟩)))
  let z' := S.cyclesMk x hx
  refine ⟨z', ?_⟩
  apply (ModuleCat.mono_iff_injective T.iCycles).mp inferInstance
  have hn := congrArg (fun m ↦ m.hom z') (ShortComplex.cyclesMap_i φ)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hn
  have hv : S.iCycles.hom z' = x := S.i_cyclesMk x hx
  exact hn.trans ((congrArg (fun k ↦ (g.f 0).hom k) hv).trans hd)

end SerrePositivity.AlgebraicGeometry
