module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.StableStructure.ConeCoconeIso

/-! cone–cocone 交換の左包含の二成分。第三 cochain の負号も保持する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory CochainComplex HomComplex DifferentialGraded
variable {R : Type u} [CommRing R] {P Q S T : Complex R}
  (f : P ⟶ Q) (g : S ⟶ T) (μ : P ⟶ S) (ν : Q ⟶ T)
  (h : Cochain P T (-1)) (hh : δ (-1) 0 h + Cochain.ofHom (μ ≫ g - f ≫ ν) = 0)
local notation "κ" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeSquareMap f g μ ν h hh
local notation "ℓ" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeSquareMap f g μ ν h hh
local notation "e" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeCoconeMap f g μ ν h hh

/-- 左包含の第一成分は、元の第一射影と同じ cone 左包含の合成。 -/
lemma dgGluingConeCoconeMap_inl_fst :
    (mappingCone.inl κ).comp
      (Cochain.ofHom (e ≫ mappingCocone.fst ℓ)) (add_zero (-1)) =
    (Cochain.ofHom (mappingCocone.fst μ)).comp (mappingCone.inl f) (zero_add (-1)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeCoconeMap_fst, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeCoconeFirst, mappingCone.inl_desc]

/-- 左包含の第三 cochain は、元の第三 cochain と係数の左包含の合成の負。 -/
lemma dgGluingConeCoconeMap_inl_snd :
    (mappingCone.inl κ).comp
      ((Cochain.ofHom e).comp (mappingCocone.snd ℓ) (zero_add (-1)))
      (by omega : -1 + -1 = -2) =
    -(mappingCocone.snd μ).comp (mappingCone.inl g) (by omega : -1 + -1 = -2) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeCoconeMap_snd, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeCoconeSecond, mappingCone.inl_descCochain]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
