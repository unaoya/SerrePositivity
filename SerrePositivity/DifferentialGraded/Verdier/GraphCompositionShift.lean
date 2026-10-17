module
public import SerrePositivity.DifferentialGraded.Verdier.GraphRestrictionShift
public import SerrePositivity.DifferentialGraded.Derived.FunctorExtensionTriangles

/-! # 既存の導来 graph 合成比較の shift 整合性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w t
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (T : Type t) [DGCategory A T] [Small.{u} T]
  (F : DGFunctor A D E) (G : DGFunctor A E T)

local instance graphCompositionDRestrictionShift :
    (dgModuleRestriction A D E F.op).onClosed.CommShift ℤ :=
  dgModuleFunctorCommShift A E D (dgModuleRestriction A D E F.op)
local instance graphCompositionERestrictionShift :
    (dgModuleRestriction A E T G.op).onClosed.CommShift ℤ :=
  dgModuleFunctorCommShift A T E (dgModuleRestriction A E T G.op)
local instance graphCompositionCompositeRestrictionShift :
    (dgModuleRestriction A D T (F.comp G).op).onClosed.CommShift ℤ :=
  dgModuleFunctorCommShift A T D (dgModuleRestriction A D T (F.comp G).op)
local instance graphCompositionDerivedDRestrictionShift :
    (dgDerivedRestriction A D E F).CommShift ℤ := dgDerivedRestrictionCommShift A D E F
local instance graphCompositionDerivedERestrictionShift :
    (dgDerivedRestriction A E T G).CommShift ℤ := dgDerivedRestrictionCommShift A E T G
local instance graphCompositionDerivedCompositeRestrictionShift :
    (dgDerivedRestriction A D T (F.comp G)).CommShift ℤ :=
  dgDerivedRestrictionCommShift A D T (F.comp G)

/-- 全 Hom の制限表示を使う、局所化前の整合的な合成比較。 -/
def graphRestrictionCompositionPreIso :
    moduleToDerived A T ⋙ (dgDerivedRestriction A E T G ⋙ dgDerivedRestriction A D E F) ≅
      moduleToDerived A T ⋙ dgDerivedRestriction A D T (F.comp G) :=
  (associator _ _ _).symm ≪≫
    isoWhiskerRight (eqToIso (dgDerivedRestriction_enriched_fac A E T G)) _ ≪≫
    associator _ _ _ ≪≫
    isoWhiskerLeft _ (eqToIso (dgDerivedRestriction_enriched_fac A D E F)) ≪≫
    (associator _ _ _).symm ≪≫
    isoWhiskerRight (graphRestrictionEnrichedCompositionIso A D E F T G) _ ≪≫
    (eqToIso (dgDerivedRestriction_enriched_fac A D T (F.comp G))).symm

instance graphRestrictionCompositionPreIsoCommShift :
    NatTrans.CommShift (graphRestrictionCompositionPreIso A D E T F G).hom ℤ := by
  let := dgDerivedRestrictionFac_commShift A E T G
  let := dgDerivedRestrictionFac_commShift A D E F
  let := dgDerivedRestrictionFac_commShift A D T (F.comp G)
  unfold graphRestrictionCompositionPreIso
  simp only [Iso.trans_hom, Iso.symm_hom, isoWhiskerRight_hom, isoWhiskerLeft_hom]
  infer_instance

lemma graphRestrictionCompositionPreIso_eq :
    (graphRestrictionCompositionPreIso A D E T F G).hom =
      whiskerLeft (moduleToDerived A T)
        (derivedGraphRestrictionCompositionIso A D E T F G).hom := by
  have he := (Localization.fullyFaithfulWhiskeringLeft
    (moduleToDerived A T) (moduleQuasiIso A T) (DerivedModuleCategory A D)).map_preimage
    (((associator _ _ _).symm ≪≫
      isoWhiskerRight (eqToIso (dgDerivedRestriction_fac A E T G)) _ ≪≫
      associator _ _ _ ≪≫
      isoWhiskerLeft _ (eqToIso (dgDerivedRestriction_fac A D E F)) ≪≫
      (associator _ _ _).symm ≪≫
      isoWhiskerRight (graphRestrictionCompositionIso A D E T F G) _ ≪≫
      (eqToIso (dgDerivedRestriction_fac A D T (F.comp G))).symm).hom)
  refine Eq.trans ?_ he.symm
  apply NatTrans.ext
  funext M
  simp only [graphRestrictionCompositionPreIso, Iso.trans_hom, Iso.symm_hom,
    isoWhiskerRight_hom, isoWhiskerLeft_hom, NatTrans.comp_app, whiskerRight_app,
    whiskerLeft_app, associator_hom_app, associator_inv_app, eqToIso.hom, eqToIso.inv, eqToHom_app,
    eqToHom_refl, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  rfl

/-- 元の導来制限合成同型そのものが、固定した標準 shift と整合する。 -/
instance derivedGraphRestrictionCompositionIsoCommShift :
    NatTrans.CommShift (derivedGraphRestrictionCompositionIso A D E T F G).hom ℤ := by
  let := (Localization.fullyFaithfulWhiskeringLeft
    (moduleToDerived A T) (moduleQuasiIso A T) (DerivedModuleCategory A D)).faithful
  apply natTransCommShift_of_precomp (moduleToDerived A T) _ (hτ := ?_)
  rw [← graphRestrictionCompositionPreIso_eq]
  infer_instance

local instance graphCompositionDerivedDExtensionShift :
    (dgDerivedExtension A D E F).CommShift ℤ := dgDerivedExtensionCommShift A D E F
local instance graphCompositionDerivedEExtensionShift :
    (dgDerivedExtension A E T G).CommShift ℤ := dgDerivedExtensionCommShift A E T G
local instance graphCompositionDerivedCompositeExtensionShift :
    (dgDerivedExtension A D T (F.comp G)).CommShift ℤ :=
  dgDerivedExtensionCommShift A D T (F.comp G)

/-- 元の導来延長合成同型を保ったまま、随伴により固定した shift との整合性を得る。 -/
instance derivedGraphExtensionCompositionIsoCommShift :
    NatTrans.CommShift (derivedGraphExtensionCompositionIso A D E T F G).hom ℤ := by
  let := dgDerivedExtensionRestrictionAdjunction_commShift A D E F
  let := dgDerivedExtensionRestrictionAdjunction_commShift A E T G
  let := dgDerivedExtensionRestrictionAdjunction_commShift A D T (F.comp G)
  let := adjunctionOfNatIsoRightCommShift (M := ℤ)
    (dgDerivedExtensionRestrictionAdjunction A D T (F.comp G))
    (derivedGraphRestrictionCompositionIso A D E T F G).symm
  exact leftAdjointUniqCommShift (M := ℤ) _ _

/-- 合成比較は三角形関手への実際の自然同型も定める。 -/
def derivedGraphExtensionCompositionTriangleIso :=
  Functor.mapTriangleIso (derivedGraphExtensionCompositionIso A D E T F G)

end SerrePositivity.DifferentialGraded
