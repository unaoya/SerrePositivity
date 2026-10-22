module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomology
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Equivalence

/-!
概要：厳密に指定整数次数へ集中した元の複体の圏で、元のホモロジー関手が圏同値であることを示す。
方針：既存の single 関手と厳密上下界からの single 表示を、元のホモロジー計算と結ぶ。
規約：元のホモロジーを保持。使われ方：集中した層の群の pro 比較を元の集中複体へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants
variable (R : Type u) [CommRing R] (d : ℤ)

def concentratedComplexProperty : ObjectProperty (Complex R) :=
  fun K => K.IsStrictlyGE d ∧ K.IsStrictlyLE d

abbrev ConcentratedComplex := (concentratedComplexProperty R d).FullSubcategory

def singleConcentratedComplex : ModuleCat.{u} R ⥤ ConcentratedComplex R d where
  obj M := ⟨(single (ModuleCat R) (ComplexShape.up ℤ) d).obj M, by
    constructor <;> infer_instance⟩
  map f := ObjectProperty.homMk ((single (ModuleCat R) (ComplexShape.up ℤ) d).map f)
  map_id M := by
    apply ObjectProperty.hom_ext
    exact (single (ModuleCat R) (ComplexShape.up ℤ) d).map_id M
  map_comp f g := by
    apply ObjectProperty.hom_ext
    exact (single (ModuleCat R) (ComplexShape.up ℤ) d).map_comp f g

lemma singleConcentratedComplex_inclusion :
    singleConcentratedComplex R d ⋙ (concentratedComplexProperty R d).ι =
      single (ModuleCat R) (ComplexShape.up ℤ) d := rfl

instance singleConcentratedComplex_faithful : (singleConcentratedComplex R d).Faithful := by
  have : (singleConcentratedComplex R d ⋙ (concentratedComplexProperty R d).ι).Faithful := by
    rw [singleConcentratedComplex_inclusion]
    infer_instance
  exact Functor.Faithful.of_comp (singleConcentratedComplex R d) (concentratedComplexProperty R d).ι

instance singleConcentratedComplex_full : (singleConcentratedComplex R d).Full := by
  have : (singleConcentratedComplex R d ⋙ (concentratedComplexProperty R d).ι).Full := by
    rw [singleConcentratedComplex_inclusion]
    infer_instance
  exact Functor.Full.of_comp_faithful (singleConcentratedComplex R d)
    (concentratedComplexProperty R d).ι

instance singleConcentratedComplex_essSurj : (singleConcentratedComplex R d).EssSurj where
  mem_essImage K := by
    have : K.obj.IsStrictlyGE d := K.property.1
    have : K.obj.IsStrictlyLE d := K.property.2
    obtain ⟨M, ⟨e⟩⟩ := CochainComplex.exists_iso_single K.obj d
    exact ⟨M, ⟨(concentratedComplexProperty R d).isoMk e.symm⟩⟩

instance singleConcentratedComplex_isEquivalence :
    (singleConcentratedComplex R d).IsEquivalence where

def concentratedComplexHomology : ConcentratedComplex R d ⥤ ModuleCat.{u} R :=
  (concentratedComplexProperty R d).ι ⋙ homologyFunctor (ModuleCat R) (ComplexShape.up ℤ) d

instance concentratedComplexHomology_isEquivalence :
    (concentratedComplexHomology R d).IsEquivalence := by
  have : (singleConcentratedComplex R d ⋙ concentratedComplexHomology R d).IsEquivalence :=
    Functor.isEquivalence_of_iso
      (homologyFunctorSingleIso (ModuleCat R) (ComplexShape.up ℤ) d).symm
  exact Functor.isEquivalence_of_comp_left (singleConcentratedComplex R d)
    (concentratedComplexHomology R d)

end SerrePositivity.KST.LocalizingInvariants
