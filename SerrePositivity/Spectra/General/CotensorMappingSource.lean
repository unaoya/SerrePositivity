module

public import SerrePositivity.Spectra.General.CotensorMappingObject
public import SerrePositivity.CategoryTheory.Adjunction.Comparison

/-! # Source naturality of C-valued cotensor mapping representability -/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace SerrePositivity.GeneralSymmetricSpectrum
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C] {K : C}

set_option maxHeartbeats 800000 in
-- Comparing the two composite Hom equivalences unfolds transported adjunctions.
lemma cotensorMappingAdjunction_naturality_source (X Z : C)
    {E E' : GeneralSymmetricSpectrum C K} (f : E ⟶ E')
    (F : GeneralSymmetricSpectrum C K) (g : pointwiseTensor X (pointwiseTensor Z E') ⟶ F) :
    (cotensorMappingAdjunction X E).homEquiv Z F
        ((pointwiseTensorFunctor X).map ((pointwiseTensorFunctor Z).map f) ≫ g) =
      (cotensorMappingAdjunction X E').homEquiv Z F g ≫
        (mappingObjectBifunctor.map f.op).app ((cotensorFunctor X).obj F) := by
  unfold cotensorMappingAdjunction
  rw [Adjunction.comp_homEquiv, Adjunction.comp_homEquiv]
  change mappingObjectHomEquiv Z E ((cotensorFunctor X).obj F)
    (pointwiseTensorHomEquiv X (pointwiseTensor Z E) F
      ((pointwiseTensorFunctor X).map ((pointwiseTensorFunctor Z).map f) ≫ g)) = _
  rw [pointwiseTensorHomEquiv_naturality_source, mappingObjectHomEquiv_naturality_source]
  rfl

lemma cotensorMappingPowerAdjunction_naturality_source (X Z : C)
    {E E' : GeneralSymmetricSpectrum C K} (f : E ⟶ E')
    (F : GeneralSymmetricSpectrum C K) (g : pointwiseTensor (X ⊗ Z) E' ⟶ F) :
    (cotensorMappingPowerAdjunction X E).homEquiv Z F
        ((pointwiseTensorFunctor (X ⊗ Z)).map f ≫ g) =
      (cotensorMappingPowerAdjunction X E').homEquiv Z F g ≫
        (ihom X).map ((mappingObjectBifunctor.map f.op).app F) := by
  unfold cotensorMappingPowerAdjunction
  rw [Adjunction.comp_homEquiv, Adjunction.comp_homEquiv]
  change (ihom.adjunction X).homEquiv Z _
    (mappingObjectHomEquiv (X ⊗ Z) E F
      ((pointwiseTensorFunctor (X ⊗ Z)).map f ≫ g)) = _
  rw [mappingObjectHomEquiv_naturality_source]
  exact (ihom.adjunction X).homEquiv_naturality_right _ _

set_option maxHeartbeats 800000 in
-- The parameter law checks the same transported composite right-adjoint types.
/-- Cotensor mapping comparison is contravariantly natural in its source. -/
lemma cotensorMappingIso_naturality_source (X : C)
    {E E' : GeneralSymmetricSpectrum C K} (f : E ⟶ E')
    (F : GeneralSymmetricSpectrum C K) :
    (mappingObjectBifunctor.map f.op).app ((cotensorFunctor X).obj F) ≫
        (cotensorMappingIso X E F).hom =
      (cotensorMappingIso X E' F).hom ≫
        (ihom X).map ((mappingObjectBifunctor.map f.op).app F) := by
  apply ActionComparisonNaturality.parameter
    (cotensorMappingAdjunction X E) (cotensorMappingAdjunction X E')
    (cotensorMappingPowerAdjunction X E) (cotensorMappingPowerAdjunction X E')
    (cotensorMappingParameterIso X E).symm (cotensorMappingParameterIso X E').symm
    (fun Z ↦ (pointwiseTensorFunctor X).map ((pointwiseTensorFunctor Z).map f))
    (fun Y ↦ (mappingObjectBifunctor.map f.op).app ((cotensorFunctor X).obj Y))
    (fun Z ↦ (pointwiseTensorFunctor (X ⊗ Z)).map f)
    (fun Y ↦ (ihom X).map ((mappingObjectBifunctor.map f.op).app Y))
  · intro Z Y g
    exact cotensorMappingAdjunction_naturality_source X Z f Y g
  · intro Z Y g
    exact cotensorMappingPowerAdjunction_naturality_source X Z f Y g
  · intro Z
    change (pointwiseTensorFunctor X).map ((pointwiseTensorFunctor Z).map f) ≫
        (pointwiseTensorAssociator X Z E').inv =
      (pointwiseTensorAssociator X Z E).inv ≫ (pointwiseTensorFunctor (X ⊗ Z)).map f
    apply (cancel_mono (pointwiseTensorAssociator X Z E').hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [pointwiseTensorAssociator_naturality]
    simp only [Iso.inv_hom_id_assoc]

/-- The cotensor mapping comparison is natural in both spectrum variables. -/
def cotensorMappingBifunctorIso (X : C) :
    mappingObjectBifunctor (K := K) ⋙
        (Functor.whiskeringLeft _ _ _).obj (cotensorFunctor X) ≅
      mappingObjectBifunctor ⋙ (Functor.whiskeringRight _ _ _).obj (ihom X) :=
  NatIso.ofComponents (fun E ↦ cotensorMappingNatIso X E.unop) (fun f ↦ by
    apply NatTrans.ext
    funext F
    exact cotensorMappingIso_naturality_source X f.unop F)

end SerrePositivity.GeneralSymmetricSpectrum
