module

public import SerrePositivity.AlgebraicGeometry.CechConstantPositiveDouble
public import SerrePositivity.AlgebraicGeometry.CechConstantPositiveTail
public import SerrePositivity.AlgebraicGeometry.CechIntegerLiftTotal

/-!
概要：同じ定数二重複体の正次数の商の全複体は完全。
方針：各行を同じ加群の正次数の列に比較し、既存の行の判定を使う。
規約：各項・微分・同じtotalの選択を保つ。
使われ方：F8の余分な定数基底列を除く比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
open scoped ZeroObject
universe u v
variable {R : Type v} [CommRing R] (A : CochainComplex (ModuleCat.{u} R) ℕ)

set_option backward.isDefEq.respectTransparency false in
/-- 同じ正次数の商の各行は元の加群の正次数の列と同型。 -/
def cechConstantPositiveDoubleRowIso (b : ℕ) :
    SerrePositivity.HomologicalAlgebra.bicomplexRow (cechConstantPositiveDouble A) b ≅
      cechConstantPositiveTail (A.X b) :=
  HomologicalComplex.Hom.isoOfComponents (fun n ↦ by cases n <;> exact Iso.refl _) (by
    intro n m hnm
    have hm : n + 1 = m := hnm
    subst m
    cases n with
    | zero =>
      change 𝟙 (0 : ModuleCat.{u} R) ≫ (cechConstantPositiveTail (A.X b)).d 0 1 =
        ((cechConstantPositiveDouble A).d 0 1).f b ≫ 𝟙 (A.X b)
      have ht : (cechConstantPositiveTail (A.X b)).d 0 1 = 0 :=
        CochainComplex.of_d (cechConstantPositiveTailTerm (A.X b))
          (cechConstantPositiveTailD (A.X b)) 0
      have hd : (cechConstantPositiveDouble A).d 0 1 = 0 :=
        CochainComplex.of_d (cechConstantPositiveDoubleTerm A) (cechConstantPositiveDoubleD A) 0
      exact (Category.id_comp _).trans
        ((ht.trans (congrArg (fun f ↦ f.f b) hd).symm).trans (Category.comp_id _).symm)
    | succ n =>
      change 𝟙 (A.X b) ≫ (cechConstantPositiveTail (A.X b)).d (n + 1) (n + 2) =
        ((cechConstantPositiveDouble A).d (n + 1) (n + 2)).f b ≫ 𝟙 (A.X b)
      have ht : (cechConstantPositiveTail (A.X b)).d (n + 1) (n + 2) =
          (cechConstantComplex (A.X b)).d (n + 1) (n + 2) := CochainComplex.of_d _ _ _
      have hd : (cechConstantPositiveDouble A).d (n + 1) (n + 2) =
          (cechConstantCochainComplex A).d (n + 1) (n + 2) := CochainComplex.of_d _ _ _
      have he := (congrArg (fun f : A ⟶ A ↦ f.f b) hd).trans
        (cechConstantCochainComplex_d_f A (n + 1) b)
      exact (Category.id_comp _).trans ((ht.trans he.symm).trans (Category.comp_id _).symm))

/-- 同じ整数係数の正次数の商の全複体は、既存の行の判定で完全。 -/
theorem cechConstantPositiveDouble_total_acyclic (A : CochainComplex (ModuleCat.{u} ℤ) ℕ) :
    (HomologicalComplex₂.total (C := ModuleCat.{u} ℤ)
      (cechConstantPositiveDouble A) (.up ℕ)).Acyclic := by
  apply cechIntegerLiftTotal_acyclic_of_rows
  intro a b
  exact (cechConstantPositiveTail_acyclic (A.X b) a).of_iso
    (cechConstantPositiveDoubleRowIso A b).symm

end SerrePositivity.AlgebraicGeometry
