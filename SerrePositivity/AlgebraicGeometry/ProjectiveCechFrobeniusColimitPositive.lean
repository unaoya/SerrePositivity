module

public import SerrePositivity.AlgebraicGeometry.ProjectiveFrobeniusColimitCech
public import SerrePositivity.AlgebraicGeometry.LinearDirectLimitColimitMap
public import SerrePositivity.AlgebraicGeometry.ReesClosedFrobeniusFunctor
public import SerrePositivity.AlgebraicGeometry.ProjectiveCechFrobeniusPositive

/-!
概要：Frobenius の係数順極限で作った Čech H の閉厚化への制限を全単射にする。
方針：実際の係数系の射を H の順極限へ自然に比較し、核・像の判定を適用する。
規約：中心外で同型な射影スキームの正次数を扱い、完備化と順極限を取り違えない。
使われ方：F6 の正次数の制限の計算。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {R A : Type u} {ι : Type} [CommRing R] [CommRing A]
variable [LinearOrder ι] [Fintype ι]
variable [Algebra R A] [Algebra (MvPolynomial ι R) A]
variable [IsScalarTower R (MvPolynomial ι R) A]
variable (G : ℕ → Submodule R A) [GradedRing G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
variable [IsNoetherianRing R] [Module.Finite (MvPolynomial ι R) A]
variable (hspan : (HomogeneousIdeal.irrelevant G).toIdeal ≤ Ideal.span
  (Set.range (fun i : ι ↦ algebraMap (MvPolynomial ι R) A (MvPolynomial.X i))))
variable (I : Ideal R)
variable [IsIso (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G) ∣_
  affineCenterComplement I)]
variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hA : (p : A) = 0)

include hspan

/-- 正次数の各段の Čech H の圏論的余極限は、実際の閉厚化への制限で全単射に移る。 -/
theorem projectiveCechFrobeniusHomologyColimit_closed_bijective (q : ℕ) (hq : 0 < q) :
    Function.Bijective
      (colim.map (Functor.whiskerRight
        (reesClosedFrobeniusCoefficientNatTrans (ι := ι) I G p hp hR hA 1)
        (fullCechComplexFunctor ⋙
          HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (.up ℕ) q))).hom := by
  let f := fun i j (_h : i ≤ j) ↦
    projectiveCechIntFrobeniusHomology (ι := ι) G p hp hR hA (j - i) q
  let g := fun i j (_h : i ≤ j) ↦
    projectiveCechIntFrobeniusHomology (ι := ι)
      (projectiveRingQuotientGrade ((I ^ 1).map (algebraMap R A)) G) p hp hR
      (frobeniusQuotientPrimeCast p hA ((I ^ 1).map (algebraMap R A))) (j - i) q
  let a := fun _ : ℕ ↦ reesClosedCechIntProjection (ι := ι) I G 1 q
  have ha : ∀ i j h x, a j (f i j h x) = g i j h (a i x) :=
    fun i j _ x ↦
      (reesClosedCechIntProjection_frobenius (ι := ι) I G p hp hR hA 1 (j - i) q x).symm
  have hb : Function.Bijective (linearDirectLimitComparison f g a ha) :=
    projectiveCechFrobeniusDirectLimit_closed_bijective G hspan I p hp hR hA q hq
  let δ := linearDirectSystemNatTrans f g a ha
  have hc : Function.Bijective (colim.map δ).hom :=
    linearDirectSystemColimitMap_bijective f g a ha hb
  have : IsIso (colim.map δ) := (ConcreteCategory.isIso_iff_bijective _).mpr hc
  let H := fullCechComplexFunctor (ι := ι) ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (.up ℕ) q
  let η := Functor.whiskerRight
    (reesClosedFrobeniusCoefficientNatTrans (ι := ι) I G p hp hR hA 1) H
  let eD := projectiveCechFrobeniusHomologyDiagramIso (ι := ι) G p hp hR hA q
  let eE := projectiveCechFrobeniusHomologyDiagramIso (ι := ι)
    (projectiveRingQuotientGrade ((I ^ 1).map (algebraMap R A)) G) p hp hR
    (frobeniusQuotientPrimeCast p hA ((I ^ 1).map (algebraMap R A))) q
  have he : η ≫ eE.hom = eD.hom ≫ δ := by
    apply NatTrans.ext
    funext n
    apply ModuleCat.hom_ext
    rfl
  have hh : colim.map η =
      (colim.mapIso eD).hom ≫ colim.map δ ≫ (colim.mapIso eE).inv := by
    apply (cancel_mono (colim.mapIso eE).hom).mp
    simpa only [Category.assoc, Functor.mapIso_hom, Functor.mapIso_inv,
      ← colim.map_comp, Iso.inv_hom_id, Category.comp_id] using
      congrArg (fun t ↦ colim.map t) he
  have : IsIso (colim.map η) := by
    rw [hh]
    infer_instance
  exact (ConcreteCategory.isIso_iff_bijective _).mp inferInstance

/-- Frobenius の係数順極限で作った正次数 Čech H の閉厚化への制限は全単射。
BST13 Lemma 3.9 の正次数の Hⁱ に用いる Čech 版。分離的なスキームの準連接層では
アフィン被覆の Čech と一致する（Stacks 30.2.6）が、この比較は形式化しない。 -/
theorem projectiveFrobeniusColimitCech_closed_bijective (q : ℕ) (hq : 0 < q) :
    Function.Bijective
      (((fullCechComplexFunctor ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (.up ℕ) q).map
          (colim.map (reesClosedFrobeniusCoefficientNatTrans (ι := ι) I G p hp hR hA 1))).hom) := by
  let η := reesClosedFrobeniusCoefficientNatTrans (ι := ι) I G p hp hR hA 1
  let H := fullCechComplexFunctor (ι := ι) ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (.up ℕ) q
  let sD := projectiveIntCechSequentialHomologyIso
    (projectiveCechFrobeniusCoefficientFunctor (ι := ι) G p hp hR hA) q
  let sE := projectiveIntCechSequentialHomologyIso
    (projectiveCechFrobeniusCoefficientFunctor (ι := ι)
      (projectiveRingQuotientGrade ((I ^ 1).map (algebraMap R A)) G) p hp hR
      (frobeniusQuotientPrimeCast p hA ((I ^ 1).map (algebraMap R A)))) q
  have hb : Function.Bijective (colim.map (Functor.whiskerRight η H)).hom :=
    projectiveCechFrobeniusHomologyColimit_closed_bijective G hspan I p hp hR hA q hq
  have : IsIso (colim.map (Functor.whiskerRight η H)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hb
  have he : H.map (colim.map η) =
      sD.hom ≫ colim.map (Functor.whiskerRight η H) ≫ sE.inv := by
    apply (cancel_mono sE.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact projectiveIntCechSequentialHomologyIso_naturality η q
  have : IsIso (H.map (colim.map η)) := by
    rw [he]
    infer_instance
  exact (ConcreteCategory.isIso_iff_bijective _).mp inferInstance

/-- 同じ Čech 複体の閉厚化への制限は、正次数の H で全単射を誘導する。 -/
theorem reesClosedFrobeniusColimitCechHomologyMap_bijective (q : ℕ) (hq : 0 < q) :
    Function.Bijective
      (reesClosedFrobeniusColimitCechHomologyMap (ι := ι) G p hp hR hA I 1 q) :=
  projectiveFrobeniusColimitCech_closed_bijective G hspan I p hp hR hA q hq

end SerrePositivity.AlgebraicGeometry
