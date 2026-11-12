module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathMapLaws

/-!
概要：元の経路代数の比較 cochain の微分を、両端射の差へ同定する。
方針：元の mapping cocone の境界式を、実両端評価へ戻す。
規約：前合成後も同じ符号を保持。使われ方：pullback 上の実経路の鎖写像条件。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.Path
variable (R : Type u) [CommRing R] (A : Mon (Complex R))

lemma primitive_boundary : δ (-1) 0 (primitive R A) +
    Cochain.ofHom ((source R A).hom - (target R A).hom) = 0 := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCocone_snd_boundary (difference R A)
  change δ (-1) 0 (primitive R A) +
    Cochain.ofHom (endpointsHom R A ≫ difference R A) = 0 at h
  rw [endpointsHom_difference] at h
  exact h

lemma primitive_precompose_boundary {K : Complex R} (a : K ⟶ (algebra R A).X) :
    δ (-1) 0 ((Cochain.ofHom a).comp (primitive R A) (zero_add (-1))) +
      Cochain.ofHom (a ≫ (source R A).hom - a ≫ (target R A).hom) = 0 := by
  have h := congrArg (fun t => (Cochain.ofHom a).comp t (zero_add 0)) (primitive_boundary R A)
  simpa only [Cochain.comp_add, Cochain.comp_zero, ← δ_ofHom_comp, ← Cochain.ofHom_comp,
    Preadditive.comp_sub] using h

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.Path
