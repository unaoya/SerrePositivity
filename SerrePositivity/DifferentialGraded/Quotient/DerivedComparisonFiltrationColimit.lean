module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonFiltration
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.LinearAlgebra.Span.Defs

/-! # 最終 dg 商 Hom は長さ部分複体の逐次余極限

各次数での有限長支持と、単射な包含の filtered colimit を用いる。
複体や Hom の有界性は仮定しない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def lengthDiagram (S : Set D) (x y : D) : ℕ ⥤ Complex A where
  obj n := lengthComplex A D S x y n
  map f := lengthMap A D S x y (leOfHom f)
  map_id n := lengthMap_refl A D S x y n
  map_comp f g := (lengthMap_comp A D S x y (leOfHom f) (leOfHom g)).symm

/-- 全長さ部分複体の最終 Hom への包含 cocone。 -/
def lengthCocone (S : Set D) (x y : D) : Cocone (lengthDiagram A D S x y) where
  pt := quotientHom A D S x y
  ι.app n := lengthInclusion A D S x y n
  ι.naturality {m n} f := by
    change lengthMap A D S x y (leOfHom f) ≫ lengthInclusion A D S x y n =
      lengthInclusion A D S x y m ≫ 𝟙 _
    rw [Category.comp_id]
    exact lengthMap_inclusion A D S x y (leOfHom f)

lemma exists_lengthSubmodule (S : Set D) (x y : D) (i : ℤ)
    (z : (internalHom A D S x y).X i) : ∃ n : ℕ, z ∈ lengthSubmodule A D S x y n i := by
  have hz : z ∈ ⨆ n : ℕ, lengthSubmodule A D S x y n i := by
    rw [lengthSubmodule_exhaustive]
    trivial
  exact (Submodule.mem_iSup_of_directed _
    (fun m n => ⟨max m n, lengthSubmodule_mono A D S x y (le_max_left m n) i,
      lengthSubmodule_mono A D S x y (le_max_right m n) i⟩)).1 hz

/-- 各次数で、長さの単射な包含の cocone は余極限。 -/
def lengthCocone_eval_isColimit (S : Set D) (x y : D) (i : ℤ) :
    IsColimit ((HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) i).mapCocone
      (lengthCocone A D S x y)) := by
  have : ReflectsFilteredColimitsOfSize.{0, 0} (forget (ModuleCat.{u} A)) :=
    reflectsSmallestFilteredColimits_of_reflectsFilteredColimits (forget (ModuleCat.{u} A))
  apply isColimitOfReflects (forget (ModuleCat.{u} A))
  apply Types.FilteredColimit.isColimitOf'
  · intro z
    obtain ⟨n, hn⟩ := exists_lengthSubmodule A D S x y i z
    exact ⟨n, ⟨z, hn⟩, rfl⟩
  · intro n z t h
    have ht : z = t := Subtype.ext h
    exact ⟨n, 𝟙 n, by rw [ht]⟩

/-- 最終微分を含む Hom 全体を、有界長部分複体の逐次余極限として復元する。 -/
def lengthCocone_isColimit (S : Set D) (x y : D) : IsColimit (lengthCocone A D S x y) :=
  HomologicalComplex.isColimitOfEval _ _ (lengthCocone_eval_isColimit A D S x y)

def lengthColimitIso (S : Set D) (x y : D) :
    colimit (lengthDiagram A D S x y) ≅ quotientHom A D S x y :=
  (colimit.isColimit _).coconePointUniqueUpToIso (lengthCocone_isColimit A D S x y)

@[reassoc] lemma lengthColimitIso_ι (S : Set D) (x y : D) (n : ℕ) :
    colimit.ι (lengthDiagram A D S x y) n ≫ (lengthColimitIso A D S x y).hom =
      lengthInclusion A D S x y n :=
  (colimit.isColimit _).comp_coconePointUniqueUpToIso_hom _ n

end SerrePositivity.DifferentialGraded.DGQuotient
