module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CoconeExtraction

/-! 回収した cone–cocone 比較は、元の右包含を同じ厳密 cocone 写像へ送る。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
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
local notation "g" => dgGluingCoconeExtractBottom μ ν f k hf
local notation "h" => dgGluingCoconeExtractHomotopy μ ν k
local notation "hh" => dgGluingCoconeExtractHomotopy_boundary μ ν f k hf

/-- 実後合成から回収した cone–cocone 同型の右包含は、同じ二包含の cocone 写像。 -/
lemma dgGluingCoconeExtractConeIso_inr :
    mappingCone.inr k ≫ (dgGluingCoconeExtractConeIso μ ν f k hf).hom =
    complexMappingCoconeMap ν (dgGluingCoconeExtractConeArrow μ ν f k hf)
      (mappingCone.inr f) (mappingCone.inr g)
      (dgGluingConeSquareMap_inr f g μ ν h hh).symm := by
  rw [dgGluingCoconeExtractConeIso, Iso.trans_hom, ← Category.assoc]
  rw [dgGluingConeInr_eqToIso k _
    (dgGluingCoconeExtractMap_recovery μ ν f k hf).symm]
  exact dgGluingConeCoconeMap_inr f g μ ν h hh

end SerrePositivity.InfinityCategories
