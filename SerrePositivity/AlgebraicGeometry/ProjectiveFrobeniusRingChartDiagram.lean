module

public import SerrePositivity.AlgebraicGeometry.ProjectiveChartFrobeniusRestriction
public import SerrePositivity.AlgebraicGeometry.ProjectiveFrobeniusColimitCech

/-!
概要：標準開の環の Frobenius 順極限を係数とする Čech 複体との比較。
方針：項ごとの同型で図式を移し、制限が実際の環の射であることを照合する。
規約：空の交叉と零環を除外しない。
使われ方：F6 の正次数の計算を実際の標準開環のモデルへ渡す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
universe u
variable {R A : Type u} {ι : Type} [CommRing R] [CommRing A]
variable [LinearOrder ι] [Fintype ι]
variable [Algebra R A] [Algebra (MvPolynomial ι R) A]
variable [IsScalarTower R (MvPolynomial ι R) A]
variable (G : ℕ → Submodule R A) [GradedRing G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hA : (p : A) = 0)

/-- 各標準開の実際の環の Frobenius 順極限を整数加群の係数図式にする。 -/
def projectiveFrobeniusRingChartDiagram : Finset ι ⥤ ModuleCat.{u} ℤ where
  obj T := ModuleCat.of ℤ (FrobeniusDirectLimit
    (HomogeneousLocalization.Away G
      (algebraMap (MvPolynomial ι R) A (projectiveLaurentDenominator R T)))
    p hp (projectiveHomogeneousChart_primeCast G p hR T))
  map {T U} h := (projectiveChartFrobeniusRingColimitIso G p hp hR hA T).inv ≫
    (colimit (projectiveCechFrobeniusCoefficientFunctor (ι := ι) G p hp hR hA)).map h ≫
      (projectiveChartFrobeniusRingColimitIso G p hp hR hA U).hom
  map_id T := by simp
  map_comp f g := by simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]

/-- 移した図式の制限は実際の環の制限が誘導する Frobenius 順極限の射。 -/
theorem projectiveFrobeniusRingChartDiagram_map {T U : Finset ι} (h : T ⊆ U) :
    (projectiveFrobeniusRingChartDiagram (ι := ι) G p hp hR hA).map (homOfLE h) =
      ModuleCat.ofHom (frobeniusDirectLimitMap p hp
        (projectiveHomogeneousChart_primeCast G p hR T)
        (projectiveHomogeneousChart_primeCast G p hR U)
        (projectiveHomogeneousChartRestrictionRingHom G h)).toAddMonoidHom.toIntLinearMap := by
  change (projectiveChartFrobeniusRingColimitIso G p hp hR hA T).inv ≫ _ ≫ _ = _
  rw [projectiveChartFrobeniusRingColimitIso_restriction]
  simp only [Iso.inv_hom_id_assoc]

/-- Frobenius 係数順極限と標準開の環の順極限との、標準開に関する自然同型。 -/
def projectiveFrobeniusRingChartDiagramIso :
    colimit (projectiveCechFrobeniusCoefficientFunctor (ι := ι) G p hp hR hA) ≅
      projectiveFrobeniusRingChartDiagram (ι := ι) G p hp hR hA :=
  NatIso.ofComponents (projectiveChartFrobeniusRingColimitIso G p hp hR hA) (by
    intro T U h
    change _ ≫ _ = _ ≫ (projectiveChartFrobeniusRingColimitIso G p hp hR hA T).inv ≫ _ ≫ _
    rw [Iso.hom_inv_id_assoc])

/-- Frobenius 係数の Čech 複体は、標準開の実際の環の順極限の Čech 複体と同型。 -/
def projectiveFrobeniusRingChartCechIso :
    projectiveFrobeniusColimitCechComplex (ι := ι) G p hp hR hA ≅
      fullCechComplex (projectiveFrobeniusRingChartDiagram (ι := ι) G p hp hR hA) :=
  (fullCechComplexFunctor (R := ℤ) (ι := ι)).mapIso
    (projectiveFrobeniusRingChartDiagramIso (ι := ι) G p hp hR hA)

end SerrePositivity.AlgebraicGeometry
