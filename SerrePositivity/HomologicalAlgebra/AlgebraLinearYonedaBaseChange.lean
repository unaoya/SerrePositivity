module
public import SerrePositivity.HomologicalAlgebra.AlgebraLinearYoneda

/-! # Actual coefficient-linear Hom adjunction for chain complexes -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- Extension/restriction adjunction is linear over the coefficient algebra
on the actual Hom modules used by coefficient dual complexes. -/
def extendScalarsHomLinearEquiv (P : ModuleCat.{u} R) (M : ModuleCat.{u} S) :
    (((ModuleCat.extendScalars (algebraMap R S)).obj P) ⟶ M) ≃ₗ[S]
      (P ⟶ (ModuleCat.restrictScalars (algebraMap R S)).obj M) where
  toEquiv := ModuleCat.ExtendRestrictScalarsAdj.homEquiv (algebraMap R S) (X := P) (Y := M)
  map_add' f g := by
    apply ModuleCat.hom_ext
    ext x
    rfl
  map_smul' s f := by
    apply ModuleCat.hom_ext
    ext x
    rfl

/-- Hom after termwise coefficient extension is the actual coefficient-algebra dual. -/
def chainLinearYonedaBaseChangeIso (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (M : ModuleCat.{u} S) :
    ((chainLinearYonedaFunctor
      (((ModuleCat.extendScalars (algebraMap R S)).mapHomologicalComplex (.down ℕ)).obj K)).obj M) ≅
        (algebraLinearYonedaFunctor (C := S) K).obj M :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => (extendScalarsHomLinearEquiv (K.X i) M).toModuleIso) (by
      intro i j hij
      apply ModuleCat.hom_ext
      ext f
      rfl)

/-- The extension/restriction comparison is natural in all coefficient maps. -/
def chainLinearYonedaBaseChangeNatIso (K : ChainComplex (ModuleCat.{u} R) ℕ) :
    chainLinearYonedaFunctor
        (((ModuleCat.extendScalars (algebraMap R S)).mapHomologicalComplex (.down ℕ)).obj K) ≅
      algebraLinearYonedaFunctor (C := S) K :=
  NatIso.ofComponents (chainLinearYonedaBaseChangeIso K) (by
    intro M N f
    ext i g
    rfl)

/-- The comparison respects precomposition by arbitrary chain maps. -/
lemma chainLinearYonedaBaseChangeNatIso_chain_map
    {K L : ChainComplex (ModuleCat.{u} R) ℕ} (f : K ⟶ L) :
    chainLinearYonedaMap
        (((ModuleCat.extendScalars (algebraMap R S)).mapHomologicalComplex (.down ℕ)).map f) ≫
        (chainLinearYonedaBaseChangeNatIso (S := S) K).hom =
      (chainLinearYonedaBaseChangeNatIso (S := S) L).hom ≫ algebraLinearYonedaMap (C := S) f := by
  apply NatTrans.ext
  funext M
  ext i g
  rfl

/-- Chain isomorphisms induce natural isomorphisms of the actual coefficient duals. -/
def chainLinearYonedaMapIso {K L : ChainComplex (ModuleCat.{u} R) ℕ} (E : K ≅ L) :
    chainLinearYonedaFunctor L ≅ chainLinearYonedaFunctor K where
  hom := chainLinearYonedaMap E.hom
  inv := chainLinearYonedaMap E.inv
  hom_inv_id := by
    rw [← chainLinearYonedaMap_comp, E.inv_hom_id, chainLinearYonedaMap_id]
  inv_hom_id := by
    rw [← chainLinearYonedaMap_comp, E.hom_inv_id, chainLinearYonedaMap_id]

end SerrePositivity
