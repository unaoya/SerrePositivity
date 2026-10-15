module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.SubcomplexTensor
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Simplex
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Induced

/-! # The boundary simplex presentation and the Reedy latching index -/

@[expose] public section
universe v
noncomputable section
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.Reedy

namespace SerrePositivity.HomotopyFunctionComplex.BoundaryIndex
variable (n : ℕ)

abbrev X := (SSet.boundary.{v} n).toSSet

lemma simplexMap_mono (x : (X.{v} n).N) :
    Mono (SubcomplexTensor.simplexMap (SSet.boundary.{v} n) x) := by
  have : Mono ((SSet.yonedaEquiv (X := X.{v} n)).symm x.simplex) :=
    SSet.Nonsingular.mono' _ x.nonDegenerate
  apply SSet.stdSimplex.mono_of_mono_map
  rw [Functor.FullyFaithful.map_preimage]
  infer_instance

abbrev indexObj (x : (X.{v} n).N) : LatchingIndex simplex (SimplexCategory.mk n) :=
  ⟨Over.mk (SubcomplexTensor.simplexMap (SSet.boundary.{v} n) x), simplexMap_mono n x,
    fun hi ↦ by
      have he := congrArg SimplexCategory.len (identities_endpoints _ hi)
      exact (ne_of_lt ((X.{v} n).dim_lt_of_nonDegenerate ⟨x.simplex, x.nonDegenerate⟩ n)) he⟩

abbrev toLatching : (X.{v} n).N ⥤ LatchingIndex simplex (SimplexCategory.mk n) where
  obj := indexObj n
  map φ := ObjectProperty.homMk (Over.homMk (SSet.N.monoOfLE (leOfHom φ))
    ((SubcomplexTensor.simplexCocone (SSet.boundary.{v} n)).w φ))
  map_id x := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    exact SSet.N.monoOfLE_refl x
  map_comp φ ψ := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    exact (SSet.N.monoOfLE_comp (leOfHom φ) (leOfHom ψ)).symm

lemma simplex_naturality {x y : (X.{v} n).N}
    (φ : indexObj n x ⟶ indexObj n y) :
    (X.{v} n).map φ.hom.left.op y.simplex = x.simplex := by
  have hw : SSet.stdSimplex.map φ.hom.left ≫ (SSet.yonedaEquiv (X := X.{v} n)).symm y.simplex =
      (SSet.yonedaEquiv (X := X.{v} n)).symm x.simplex := by
    apply (cancel_mono (SSet.boundary.{v} n).ι).mp
    calc
      _ = SSet.stdSimplex.map φ.hom.left ≫
          SSet.stdSimplex.map (SubcomplexTensor.simplexMap (SSet.boundary.{v} n) y) :=
        (Category.assoc _ _ _).trans (congrArg (fun f ↦ SSet.stdSimplex.map φ.hom.left ≫ f)
          (SSet.stdSimplex.fullyFaithful.map_preimage _).symm)
      _ = SSet.stdSimplex.map (SubcomplexTensor.simplexMap (SSet.boundary.{v} n) x) :=
        (SSet.stdSimplex.map_comp _ _).symm.trans (congrArg SSet.stdSimplex.map (Over.w φ.hom))
      _ = _ := SSet.stdSimplex.fullyFaithful.map_preimage _
  have h := SSet.yonedaEquiv_naturality φ.hom.left
    ((SSet.yonedaEquiv (X := X.{v} n)).symm y.simplex)
  simpa only [Equiv.apply_symm_apply] using h.trans (congrArg SSet.yonedaEquiv hw)

def fullyFaithful : (toLatching.{v} n).FullyFaithful where
  preimage φ := homOfLE (SSet.N.le_iff_exists_mono.mpr
    ⟨φ.hom.left, latching_map_direct simplex φ, simplex_naturality n φ⟩)
  map_preimage φ := by
    have : Mono φ.hom.left := latching_map_direct simplex φ
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    exact (SSet.N.monoOfLE_eq_iff _ φ.hom.left).mpr (simplex_naturality n φ)
  preimage_map φ := Subsingleton.elim _ _

abbrev boundarySimplex (f : LatchingIndex simplex (SimplexCategory.mk n)) :
    (X.{v} n).obj (Opposite.op f.obj.left) :=
  ⟨SSet.stdSimplex.objEquiv.symm f.obj.hom, by
    change ¬Function.Surjective f.obj.hom.toOrderHom
    intro hf
    have hep : Epi f.obj.hom := SimplexCategory.epi_iff_surjective.mpr hf
    exact f.property.2 (simplex.identities_of_prop₂_of_eq f.property.1
      (le_antisymm (@SimplexCategory.len_le_of_mono _ _ f.obj.hom f.property.1)
        (@SimplexCategory.len_le_of_epi _ _ f.obj.hom hep)))⟩

lemma boundarySimplex_nonDegenerate (f : LatchingIndex simplex (SimplexCategory.mk n)) :
    boundarySimplex.{v} n f ∈ (X.{v} n).nonDegenerate f.obj.left.len := by
  rw [SSet.Subcomplex.mem_nonDegenerate_iff]
  exact (SSet.stdSimplex.objEquiv_symm_mem_nonDegenerate_iff_mono f.obj.hom).mpr f.property.1

abbrev fromLatching (f : LatchingIndex simplex (SimplexCategory.mk n)) : (X.{v} n).N :=
  SSet.N.mk (boundarySimplex n f) (boundarySimplex_nonDegenerate n f)

lemma simplexMap_fromLatching (f : LatchingIndex simplex (SimplexCategory.mk n)) :
    SubcomplexTensor.simplexMap (SSet.boundary.{v} n) (fromLatching n f) = f.obj.hom := by
  apply SSet.stdSimplex.fullyFaithful.map_injective
  exact (SSet.stdSimplex.fullyFaithful.map_preimage _).trans
    ((SSet.yonedaEquiv_symm_comp (boundarySimplex.{v} n f) (SSet.boundary.{v} n).ι).symm.trans
      ((SSet.yonedaEquiv (X := SSet.stdSimplex.{v}.obj (SimplexCategory.mk n))).symm_apply_apply
        (SSet.stdSimplex.map f.obj.hom)))

def objectIso (f : LatchingIndex simplex (SimplexCategory.mk n)) :
    (toLatching.{v} n).obj (fromLatching n f) ≅ f :=
  ObjectProperty.isoMk _ (Over.isoMk (Iso.refl _) (by
    exact (Category.id_comp f.obj.hom).trans (simplexMap_fromLatching.{v} n f).symm))

instance toLatching_full : (toLatching.{v} n).Full := (fullyFaithful n).full
instance toLatching_faithful : (toLatching.{v} n).Faithful := (fullyFaithful n).faithful
instance toLatching_essSurj : (toLatching.{v} n).EssSurj where
  mem_essImage f := ⟨fromLatching.{v} n f, ⟨objectIso.{v} n f⟩⟩
instance toLatching_isEquivalence : (toLatching.{v} n).IsEquivalence where

abbrev equivalence : (X.{v} n).N ≌ LatchingIndex simplex (SimplexCategory.mk n) :=
  (toLatching n).asEquivalence

lemma source_eq : (equivalence.{v} n).functor ⋙
    latchingSource simplex (SimplexCategory.mk n) =
      NonsingularPresentation.diagram (X.{v} n) := rfl

end SerrePositivity.HomotopyFunctionComplex.BoundaryIndex
