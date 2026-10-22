module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomology
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Equivalence

/-!
概要：厳密に次数零へ集中した元の複体の圏で、元の H⁰ 関手が圏同値であることを示す。
方針：既存の single 関手と厳密上下界からの single 表示を、元の H⁰ 計算と結ぶ。
規約：元のホモロジーを保持。使われ方：π₀ の群の pro 比較を実零切断へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants
variable (R : Type u) [CommRing R]

def zeroComplexProperty : ObjectProperty (Complex R) :=
  fun K => K.IsStrictlyGE 0 ∧ K.IsStrictlyLE 0

abbrev ZeroComplex := (zeroComplexProperty R).FullSubcategory

def singleZeroComplex : ModuleCat.{u} R ⥤ ZeroComplex R where
  obj M := ⟨(single (ModuleCat R) (ComplexShape.up ℤ) 0).obj M, by
    constructor <;> infer_instance⟩
  map f := ObjectProperty.homMk ((single (ModuleCat R) (ComplexShape.up ℤ) 0).map f)
  map_id M := by
    apply ObjectProperty.hom_ext
    exact (single (ModuleCat R) (ComplexShape.up ℤ) 0).map_id M
  map_comp f g := by
    apply ObjectProperty.hom_ext
    exact (single (ModuleCat R) (ComplexShape.up ℤ) 0).map_comp f g

lemma singleZeroComplex_inclusion :
    singleZeroComplex R ⋙ (zeroComplexProperty R).ι =
      single (ModuleCat R) (ComplexShape.up ℤ) 0 := rfl

instance singleZeroComplex_faithful : (singleZeroComplex R).Faithful := by
  have : (singleZeroComplex R ⋙ (zeroComplexProperty R).ι).Faithful := by
    rw [singleZeroComplex_inclusion]
    infer_instance
  exact Functor.Faithful.of_comp (singleZeroComplex R) (zeroComplexProperty R).ι

instance singleZeroComplex_full : (singleZeroComplex R).Full := by
  have : (singleZeroComplex R ⋙ (zeroComplexProperty R).ι).Full := by
    rw [singleZeroComplex_inclusion]
    infer_instance
  exact Functor.Full.of_comp_faithful (singleZeroComplex R) (zeroComplexProperty R).ι

instance singleZeroComplex_essSurj : (singleZeroComplex R).EssSurj where
  mem_essImage K := by
    have : K.obj.IsStrictlyGE 0 := K.property.1
    have : K.obj.IsStrictlyLE 0 := K.property.2
    obtain ⟨M, ⟨e⟩⟩ := CochainComplex.exists_iso_single K.obj 0
    exact ⟨M, ⟨(zeroComplexProperty R).isoMk e.symm⟩⟩

instance singleZeroComplex_isEquivalence : (singleZeroComplex R).IsEquivalence where

def zeroComplexHomology : ZeroComplex R ⥤ ModuleCat.{u} R :=
  (zeroComplexProperty R).ι ⋙ homologyFunctor (ModuleCat R) (ComplexShape.up ℤ) 0

instance zeroComplexHomology_isEquivalence : (zeroComplexHomology R).IsEquivalence := by
  have : (singleZeroComplex R ⋙ zeroComplexHomology R).IsEquivalence :=
    Functor.isEquivalence_of_iso
      (homologyFunctorSingleIso (ModuleCat R) (ComplexShape.up ℤ) 0).symm
  exact Functor.isEquivalence_of_comp_left (singleZeroComplex R) (zeroComplexHomology R)

end SerrePositivity.KST.LocalizingInvariants
