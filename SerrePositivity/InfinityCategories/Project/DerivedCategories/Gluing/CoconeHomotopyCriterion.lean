module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CoconeExtraction
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated

/-! 同じ射影を保つ cocone 写像の、回収した両成分によるホモトピー同型判定。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R]
local notation "Qh" => _root_.HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)

/-- 複体の射は、標準 cone がホモトピー圏で零であるとき、かつそのときに限り同型。 -/
lemma dgGluingComplexCone_isZero_iff {P S : Complex R} (f : P ⟶ S) :
    IsZero ((Qh).obj (mappingCone f)) ↔ IsIso ((Qh).map f) :=
  CategoryTheory.Pretriangulated.Triangle.isZero₃_iff_isIso₁ (mappingCone.triangleh f)
    (_root_.HomotopyCategory.mappingCone_triangleh_distinguished f)

/-- 両端がホモトピー圏で零なら、同じ射の標準 cocone も零。 -/
lemma dgGluingComplexCocone_isZero {P S : Complex R} (f : P ⟶ S)
    (hP : IsZero ((Qh).obj P)) (hS : IsZero ((Qh).obj S)) :
    IsZero ((Qh).obj (mappingCocone f)) := by
  have hc : IsZero ((Qh).obj (mappingCone f)) :=
    CategoryTheory.Pretriangulated.Triangle.isZero₃_of_isZero₁₂ (mappingCone.triangleh f)
      (_root_.HomotopyCategory.mappingCone_triangleh_distinguished f) hP hS
  have hs := (CategoryTheory.shiftFunctor
    (_root_.HomotopyCategory (ModuleCat R) (ComplexShape.up ℤ)) (-1 : ℤ)).map_isZero hc
  exact hs.of_iso (((Qh).commShiftIso (-1 : ℤ)).app (mappingCone f))

variable {P S P' S' : Complex R} (μ : P ⟶ S) (ν : P' ⟶ S') (f : P ⟶ P')
  (k : mappingCocone μ ⟶ mappingCocone ν)
  (hk : k ≫ mappingCocone.fst ν = mappingCocone.fst μ ≫ f)

/-- 第一射影を保つ実 cocone 写像は、上辺と回収した下辺が K で同型なら K で同型。 -/
lemma dgGluingCoconeExtract_isIso
    (hf : IsIso ((Qh).map f))
    (hg : IsIso ((Qh).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeExtractBottom μ ν f k hk))) :
    IsIso ((Qh).map k) := by
  have hcf := (dgGluingComplexCone_isZero_iff R f).2 hf
  have hcg := (dgGluingComplexCone_isZero_iff R
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeExtractBottom μ ν f k hk)).2 hg
  have hz := dgGluingComplexCocone_isZero R
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeExtractConeArrow μ ν f k hk) hcf hcg
  exact (dgGluingComplexCone_isZero_iff R k).1
    (hz.of_iso ((Qh).mapIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeExtractConeIso μ ν f k hk)))

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
