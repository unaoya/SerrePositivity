module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathMap
public import SerrePositivity.KST.LocalizingInvariants.CochainMappingCoconeMapSurjective
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-!
概要：経路代数の関手は、実代数射の各次数の全射性を保つ。
方針：二直和上の全射性を評価し、mapping cocone の二斉次成分を持ち上げる。
規約：準同型性とは独立の主張。使われ方：全射準同型に対する相対経路。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.Path
variable (R : Type u) [CommRing R] {A B : Mon (Complex R)} (f : A ⟶ B)
  (hs : ∀ n : ℤ, Function.Surjective (f.hom.f n))

include hs in
lemma map_surjective (n : ℤ) : Function.Surjective ((map R f).hom.f n) := by
  have he : ∀ i, Epi (f.hom.f i) := fun i => (ModuleCat.epi_iff_surjective _).2 (hs i)
  have : Epi f.hom := HomologicalComplex.epi_of_epi_f _ he
  have : Epi (biprod.map f.hom f.hom) := inferInstance
  have ha : Function.Surjective ((biprod.map f.hom f.hom).f n) :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  exact cochainMappingCoconeMap_surjective (difference R A) (difference R B)
    (biprod.map f.hom f.hom) f.hom (difference_naturality R f) n ha (hs (n - 1))

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.Path
