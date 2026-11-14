module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ConeComparisons.CoconeExtraction

/-! 回収した cone–cocone 比較は、元の右包含を同じ厳密 cocone 写像へ送る。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory CochainComplex HomComplex DifferentialGraded
variable {R : Type u} [CommRing R] {P Q S T : Complex R}

/-- cone の基になる鎖写像の等式による移送は、標準右包含を保つ。 -/
lemma dgGluingConeInr_eqToIso (f g : P ⟶ Q) (h : f = g) :
    mappingCone.inr f ≫ (eqToIso (congrArg (fun a : P ⟶ Q => mappingCone a) h)).hom =
      mappingCone.inr g := by
  subst g
  simp

variable (μ : P ⟶ Q) (ν : S ⟶ T) (f : P ⟶ S)
  (k : mappingCocone μ ⟶ mappingCocone ν)
  (hf : k ≫ mappingCocone.fst ν = mappingCocone.fst μ ≫ f)
local notation "g" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeExtractBottom μ ν f k hf
local notation "h" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeExtractHomotopy μ ν k
local notation "hh" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeExtractHomotopy_boundary μ ν f k hf

/-- 実後合成から回収した cone–cocone 同型の右包含は、同じ二包含の cocone 写像。 -/
lemma dgGluingCoconeExtractConeIso_inr :
    mappingCone.inr k ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeExtractConeIso μ ν f k hf).hom =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap ν (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeExtractConeArrow μ ν f k hf)
      (mappingCone.inr f) (mappingCone.inr g)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeSquareMap_inr f g μ ν h hh).symm := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeExtractConeIso, Iso.trans_hom, ← Category.assoc]
  rw [dgGluingConeInr_eqToIso k _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeExtractMap_recovery μ ν f k hf).symm]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeCoconeMap_inr f g μ ν h hh

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
