module

public import SerrePositivity.BhattScholze.RootedExtension.DeltaRoot.DeltaRootRelationCoefficientFlat

/-! # 根添加を入れた具体的δ除算包のraw残余商 -/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (D : DeltaStructure p A) (d : A) (b : σ → A)

/-- rank-one多項式δ環でCdにより根関係を除算した既存添加環のraw残余商。 -/
abbrev DeltaRootAdjoinDivisionResidue :=
  DeltaAdjoinDivisionResidue (polynomialRankOneDeltaStructure σ D) (MvPolynomial.C d)
    (deltaRootRelationFamily (p := p) b)

/-- 根を表す元は、源多項式変数の既存δ係数射による標準残余商像。 -/
def deltaRootAdjoinDivisionResidueVariable (s : σ) : DeltaRootAdjoinDivisionResidue D d b :=
  Ideal.Quotient.mk _ (deltaAdjoinDivisionMap (polynomialRankOneDeltaStructure σ D)
    (MvPolynomial.C d) (deltaRootRelationFamily (p := p) b) (MvPolynomial.X s))

/-- 基底のδdを表す単元は、源rank-one多項式δ環のCdのδ値を表す。 -/
theorem deltaRootPolynomialUnit_delta (u : Aˣ) (hu : (u : A) = D.delta d) :
    ((u.map (MvPolynomial.C : A →+* MvPolynomial σ A) : (MvPolynomial σ A)ˣ) :
      MvPolynomial σ A) = (polynomialRankOneDeltaStructure σ D).delta (MvPolynomial.C d) := by
  change MvPolynomial.C (u : A) = _
  rw [hu, polynomialRankOneDeltaStructure_delta_C]

variable (hpB : Function.Injective (fun f : MvPolynomial σ A => (p : MvPolynomial σ A) * f))
variable (hpL : Function.Injective (fun f : RelativeFreeDeltaRing (R := MvPolynomial σ A) σ =>
  (p : RelativeFreeDeltaRing (R := MvPolynomial σ A) σ) * f))
variable (hg : Function.Injective (WittVector.ghostMap :
  WittVector p (RelativeFreeDeltaRing (R := MvPolynomial σ A) σ) →
    ℕ → RelativeFreeDeltaRing (R := MvPolynomial σ A) σ))
variable (u : Aˣ) (hu : (u : A) = D.delta d)

/-- A/(p,d)から根添加を入れたrawδ除算残余商への具体的標準係数射。 -/
def deltaRootAdjoinDivisionResidueBaseMap :
    A ⧸ Ideal.span {(p : A), d} →+* DeltaRootAdjoinDivisionResidue D d b :=
  (deltaAdjoinDivisionResidueBaseMap (polynomialRankOneDeltaStructure σ D) hpB hpL hg
    (MvPolynomial.C d) (deltaRootRelationFamily (p := p) b)
    (u.map (MvPolynomial.C : A →+* MvPolynomial σ A))
    (deltaRootPolynomialUnit_delta D d u hu)).comp
    (deltaRootRelationCoefficientBaseMap (p := p) d b)

/-- 標準係数射は源多項式環の基底係数の既存δ係数射の残余商像に一致する。 -/
theorem deltaRootAdjoinDivisionResidueBaseMap_mk (c : A) :
    deltaRootAdjoinDivisionResidueBaseMap D d b hpB hpL hg u hu (Ideal.Quotient.mk _ c) =
      Ideal.Quotient.mk _ (deltaAdjoinDivisionMap (polynomialRankOneDeltaStructure σ D)
        (MvPolynomial.C d) (deltaRootRelationFamily (p := p) b) (MvPolynomial.C c)) := by
  rw [deltaRootAdjoinDivisionResidueBaseMap, RingHom.comp_apply,
    deltaRootRelationCoefficientBaseMap_mk, deltaAdjoinDivisionResidueBaseMap_mk]

/-- 標準係数射による根δ除算残余商のA/(p,d)代数構造。 -/
@[instance_reducible] def deltaRootAdjoinDivisionResidueBaseAlgebra :
    Algebra (A ⧸ Ideal.span {(p : A), d}) (DeltaRootAdjoinDivisionResidue D d b) :=
  (deltaRootAdjoinDivisionResidueBaseMap D d b hpB hpL hg u hu).toAlgebra

/-- 根添加を入れたrawδ除算残余商は標準係数射によってA/(p,d)上忠実平坦。 -/
theorem deltaRootAdjoinDivisionResidue_moduleFaithfullyFlat :
    letI := deltaRootAdjoinDivisionResidueBaseAlgebra D d b hpB hpL hg u hu
    Module.FaithfullyFlat (A ⧸ Ideal.span {(p : A), d}) (DeltaRootAdjoinDivisionResidue D d b) := by
  let := deltaRootRelationCoefficientBaseAlgebra (p := p) d b
  let := deltaAdjoinDivisionResidueBaseAlgebra (polynomialRankOneDeltaStructure σ D) hpB hpL hg
    (MvPolynomial.C d) (deltaRootRelationFamily (p := p) b)
    (u.map (MvPolynomial.C : A →+* MvPolynomial σ A)) (deltaRootPolynomialUnit_delta D d u hu)
  let := deltaRootAdjoinDivisionResidueBaseAlgebra D d b hpB hpL hg u hu
  let : IsScalarTower (A ⧸ Ideal.span {(p : A), d})
      (DeltaRootRelationCoefficientQuotient (p := p) d b)
      (DeltaRootAdjoinDivisionResidue D d b) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let := deltaRootRelationCoefficient_moduleFaithfullyFlat (p := p) d b
  let := deltaAdjoinDivisionResidue_moduleFaithfullyFlat (polynomialRankOneDeltaStructure σ D)
    hpB hpL hg (MvPolynomial.C d) (deltaRootRelationFamily (p := p) b)
    (u.map (MvPolynomial.C : A →+* MvPolynomial σ A)) (deltaRootPolynomialUnit_delta D d u hu)
  exact Module.FaithfullyFlat.trans _ (DeltaRootRelationCoefficientQuotient (p := p) d b) _

/-- 根添加を入れたrawδ除算残余商は標準係数射によってA/(p,d)上平坦。 -/
theorem deltaRootAdjoinDivisionResidue_moduleFlat :
    letI := deltaRootAdjoinDivisionResidueBaseAlgebra D d b hpB hpL hg u hu
    Module.Flat (A ⧸ Ideal.span {(p : A), d}) (DeltaRootAdjoinDivisionResidue D d b) := by
  let := deltaRootAdjoinDivisionResidueBaseAlgebra D d b hpB hpL hg u hu
  let := deltaRootAdjoinDivisionResidue_moduleFaithfullyFlat D d b hpB hpL hg u hu
  infer_instance

/-- rawδ除算残余商の具体的な根は、指定元の標準像をp乗根として持つ。 -/
theorem deltaRootAdjoinDivisionResidueVariable_pow (s : σ) :
    deltaRootAdjoinDivisionResidueVariable D d b s ^ p =
      deltaRootAdjoinDivisionResidueBaseMap D d b hpB hpL hg u hu (Ideal.Quotient.mk _ (b s)) := by
  let q := deltaAdjoinDivisionResidueBaseMap (polynomialRankOneDeltaStructure σ D) hpB hpL hg
    (MvPolynomial.C d) (deltaRootRelationFamily (p := p) b)
    (u.map (MvPolynomial.C : A →+* MvPolynomial σ A)) (deltaRootPolynomialUnit_delta D d u hu)
  have h := congrArg q (deltaRootRelationCoefficient_variable_pow (p := p) d b s)
  rw [map_pow, deltaAdjoinDivisionResidueBaseMap_mk] at h
  exact h

end SerrePositivity.BhattScholze
