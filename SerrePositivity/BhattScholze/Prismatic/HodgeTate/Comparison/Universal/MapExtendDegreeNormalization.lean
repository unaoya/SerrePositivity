module

public import SerrePositivity.HomologicalAlgebra.MapExtend
public import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# 零延長と係数関手の指定同型の非負次数

## 概要
零延長と係数関手の標準同型を、元の非負次数への指定同型で評価する。

## 方針
定義に用いた次数の選択は、自然数の整数への単射性で元の次数と一致する。

## 規約
指定された零延長の同型を変えない。

## 使われ方
元の被覆係数射を、元の余輪体の値で照合する。
-/

public noncomputable section
universe u
open CategoryTheory HomologicalComplex
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R S : Type u} [CommRing R] [CommRing S]

/-- 指定された零延長比較は、元の非負次数への同型と可換。 -/
theorem mapExtendIso_hom_f_nat (F : ModuleCat.{u} R ⥤ ModuleCat.{u} S) [F.Additive]
    (K : CochainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    (SerrePositivity.mapExtendIso F K ComplexShape.embeddingUpNat).hom.f (n : ℤ) ≫
        (((F.mapHomologicalComplex (.up ℕ)).obj K).extendXIso
          ComplexShape.embeddingUpNat (i := n) rfl).hom =
      F.map (K.extendXIso ComplexShape.embeddingUpNat (i := n) rfl).hom := by
  classical
  have hi : ∃ j : ℕ, ComplexShape.embeddingUpNat.f j = (n : ℤ) := ⟨n, rfl⟩
  change (SerrePositivity.mapExtendXIso F K ComplexShape.embeddingUpNat (n : ℤ)).hom ≫ _ = _
  simp only [SerrePositivity.mapExtendXIso, dite_eq_left hi, Iso.trans_hom,
    Functor.mapIso_hom, Iso.symm_hom]
  simp [HomologicalComplex.extendXIso, HomologicalComplex.extend.XIso, eqToHom_map]

/-- 元の指定比較の逆も、元の非負次数への同型と可換。 -/
theorem mapExtendIso_inv_f_nat (F : ModuleCat.{u} R ⥤ ModuleCat.{u} S) [F.Additive]
    (K : CochainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    (SerrePositivity.mapExtendIso F K ComplexShape.embeddingUpNat).inv.f (n : ℤ) ≫
        F.map (K.extendXIso ComplexShape.embeddingUpNat (i := n) rfl).hom =
      (((F.mapHomologicalComplex (.up ℕ)).obj K).extendXIso
        ComplexShape.embeddingUpNat (i := n) rfl).hom := by
  rw [← mapExtendIso_hom_f_nat F K n]
  let d := (HomologicalComplex.eval (ModuleCat.{u} S) (.up ℤ) (n : ℤ)).mapIso
    (SerrePositivity.mapExtendIso F K ComplexShape.embeddingUpNat)
  change d.inv ≫ d.hom ≫ _ = _
  simp only [Iso.inv_hom_id_assoc]

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
