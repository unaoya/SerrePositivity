module
public import SerrePositivity.DifferentialGraded.Verdier.DerivedGraphComposition
public import SerrePositivity.DifferentialGraded.Derived.RestrictionTriangles
public import SerrePositivity.DifferentialGraded.Verdier.AdjunctionComparisonShift
public import SerrePositivity.DifferentialGraded.Verdier.ShiftReflection

/-! # graph 制限の合成比較と既存 shift の整合性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w t
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Functor Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

local instance restrictionCompositionShift :
    (dgModuleRestriction A D E F.op).onClosed.CommShift ℤ :=
  dgModuleFunctorCommShift A E D (dgModuleRestriction A D E F.op)

/-- 制限の正規化 shift 比較は各評価次数で恒等射である。 -/
lemma graphRestrictionShift_hom_eval (s : ℤ) (M : ModuleCategory A E) (d : D) (i : ℤ) :
    ((moduleEvaluation A D d).map
      (((dgModuleRestriction A D E F.op).onClosed.commShiftIso s).hom.app M)).f i = 𝟙 _ := by
  change ((moduleEvaluation A D d).map
    ((normalizedDGModuleFunctorCommShiftIso A E D
      (dgModuleRestriction A D E F.op) s).hom.app M)).f i = _
  have he : (normalizedDGModuleFunctorCommShiftIso A E D
      (dgModuleRestriction A D E F.op) s).hom.app M =
      (normalizedDGModuleFunctorShiftIso A E D (dgModuleRestriction A D E F.op) s
        (ForgetEnrichment.to (Complex A) M)).hom := by
    simp only [normalizedDGModuleFunctorCommShiftIso, moduleShiftFunctor_eq]
    rfl
  rw [he, normalizedDGModuleFunctorShiftIso_hom_eval_f]
  change ((moduleHomπ A D _ _ d).f s
    ((moduleRestrictionHom A D E F.op _ _).f s
      (normalizedModuleShiftOut A E s (ForgetEnrichment.to (Complex A) M)))).v i (i + s) rfl = _
  have h := congrArg (fun k => (k.f s
    (normalizedModuleShiftOut A E s (ForgetEnrichment.to (Complex A) M))).v i (i + s) rfl)
    (moduleRestrictionHom_π A D E F.op _ _ d)
  exact h.trans (normalizedModuleShiftOut_v A E s _ (F.obj d) i)
variable (T : Type t) [DGCategory A T] [Small.{u} T] (G : DGFunctor A E T)

/-- 元の合成比較を、全 Hom の dg 制限の閉零関手として表示する。 -/
def graphRestrictionEnrichedCompositionIso :
    (dgModuleRestriction A E T G.op).onClosed ⋙ (dgModuleRestriction A D E F.op).onClosed ≅
      (dgModuleRestriction A D T (F.comp G).op).onClosed :=
  NatIso.ofComponents (fun M => (graphRestrictionCompositionIso A D E T F G).app M)
    (by
      intro M N f
      apply moduleMorphism_ext
      intro d
      simp only [Functor.comp_map, CategoryTheory.Functor.map_comp,
        dgModuleRestriction_map_eval, Iso.app_hom, graphRestrictionCompositionIso,
        NatIso.ofComponents_hom_app, moduleIsoMk_hom_eval, Iso.refl_hom]
      change (moduleEvaluation A T (G.obj (F.obj d))).map f ≫ 𝟙 _ =
        𝟙 _ ≫ (moduleEvaluation A T (G.obj (F.obj d))).map f
      exact (Category.comp_id _).trans (Category.id_comp _).symm)

local instance : (dgModuleRestriction A E T G.op).onClosed.CommShift ℤ :=
  dgModuleFunctorCommShift A T E (dgModuleRestriction A E T G.op)
local instance : (dgModuleRestriction A D T (F.comp G).op).onClosed.CommShift ℤ :=
  dgModuleFunctorCommShift A T D (dgModuleRestriction A D T (F.comp G).op)

lemma graphRestrictionEnrichedCompositionIso_eval (M : ModuleCategory A T) (d : D) :
    (moduleEvaluation A D d).map
      ((graphRestrictionEnrichedCompositionIso A D E F T G).hom.app M) = 𝟙 _ := by
  exact moduleIsoMk_hom_eval A D _ _ d

instance graphRestrictionEnrichedCompositionIsoCommShift :
    NatTrans.CommShift (graphRestrictionEnrichedCompositionIso A D E F T G).hom ℤ where
  shift_comm s := by
    apply NatTrans.ext
    funext M
    apply moduleMorphism_ext
    intro d
    apply HomologicalComplex.hom_ext
    intro i
    simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
      Functor.commShiftIso_comp_hom_app, CategoryTheory.Functor.map_comp,
      HomologicalComplex.comp_f, dgModuleRestriction_map_eval,
      graphRestrictionEnrichedCompositionIso_eval, HomologicalComplex.id_f]
    rw [graphRestrictionShift_hom_eval, graphRestrictionShift_hom_eval,
      graphRestrictionShift_hom_eval]
    change 𝟙 _ ≫ 𝟙 _ ≫
      ((moduleEvaluation A D d).map
        ((shiftFunctor (ModuleCategory A D) s).map
          ((graphRestrictionEnrichedCompositionIso A D E F T G).hom.app M))).f i = 𝟙 _ ≫ 𝟙 _
    rw [moduleShiftFunctor_eq]
    change 𝟙 _ ≫ 𝟙 _ ≫
      ((moduleEvaluation A D d).map
        (moduleShiftMap A D s
          ((graphRestrictionEnrichedCompositionIso A D E F T G).hom.app M))).f i = _
    rw [moduleShiftMap_eval, graphRestrictionEnrichedCompositionIso_eval]
    simp only [CategoryTheory.Functor.map_id, HomologicalComplex.id_f,
      Category.id_comp]
    rfl
end SerrePositivity.DifferentialGraded
