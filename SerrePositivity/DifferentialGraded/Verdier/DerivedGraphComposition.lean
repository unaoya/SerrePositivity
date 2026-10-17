module
public import SerrePositivity.DifferentialGraded.Derived.FunctorExtensionAdjunction
public import SerrePositivity.DifferentialGraded.Module.Isomorphism
public import Mathlib.CategoryTheory.Adjunction.Unique

/-! # 導来 graph 延長の合成比較

置換の合成を同一視せず、実際の導来制限と随伴の一意性を使う。
-/
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

private lemma postcompose_identity (P Q : Complex A) : homPostcompose P (𝟙 Q) = 𝟙 _ :=
  (homFunctor P).map_id Q

private lemma precompose_identity (P Q : Complex A) : homPrecompose (𝟙 P) Q = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  exact CochainComplex.HomComplex.Cochain.id_comp z

def graphRestrictionCompositionIso :
    moduleRestriction A E T G.op ⋙ moduleRestriction A D E F.op ≅
      moduleRestriction A D T (F.comp G).op :=
  NatIso.ofComponents (fun M => moduleIsoMk A D (fun _ => Iso.refl _) (by
    intro x y
    change (F.map y.unop x.unop ≫
      (G.map (F.obj y.unop) (F.obj x.unop) ≫
        (ForgetEnrichment.to (Complex A) M).map (Opposite.op (G.obj (F.obj x.unop)))
          (Opposite.op (G.obj (F.obj y.unop))))) ≫ _ =
      ((F.map y.unop x.unop ≫ G.map (F.obj y.unop) (F.obj x.unop)) ≫
        (ForgetEnrichment.to (Complex A) M).map (Opposite.op (G.obj (F.obj x.unop)))
          (Opposite.op (G.obj (F.obj y.unop)))) ≫ _
    dsimp only [Iso.refl_hom]
    rw [postcompose_identity, precompose_identity]
    simp only [Category.assoc]
    rfl))
    (by
      intro M N f
      apply moduleMorphism_ext
      intro x
      simp only [CategoryTheory.Functor.map_comp, moduleIsoMk_hom_eval,
        Iso.refl_hom, Functor.comp_map, moduleRestriction_map_eval]
      change (moduleEvaluation A T (G.obj (F.obj x))).map f ≫ 𝟙 _ =
        𝟙 _ ≫ (moduleEvaluation A T (G.obj (F.obj x))).map f
      simp only [Category.comp_id, Category.id_comp])

def derivedGraphRestrictionCompositionIso :
    dgDerivedRestriction A E T G ⋙ dgDerivedRestriction A D E F ≅
      dgDerivedRestriction A D T (F.comp G) :=
  (Localization.fullyFaithfulWhiskeringLeft (moduleToDerived A T) (moduleQuasiIso A T)
    (DerivedModuleCategory A D)).preimageIso
    ((Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (eqToIso (dgDerivedRestriction_fac A E T G)) _ ≪≫
      Functor.associator _ _ _ ≪≫
      isoWhiskerLeft _ (eqToIso (dgDerivedRestriction_fac A D E F)) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (graphRestrictionCompositionIso A D E T F G) _ ≪≫
      (eqToIso (dgDerivedRestriction_fac A D T (F.comp G))).symm)

/-- 任意の dg 関手の導来 graph 延長は、関手の合成と自然同型で両立する。 -/
def derivedGraphExtensionCompositionIso :
    dgDerivedExtension A D E F ⋙ dgDerivedExtension A E T G ≅
      dgDerivedExtension A D T (F.comp G) :=
  Adjunction.leftAdjointUniq
    ((dgDerivedExtensionRestrictionAdjunction A D E F).comp
      (dgDerivedExtensionRestrictionAdjunction A E T G))
    ((dgDerivedExtensionRestrictionAdjunction A D T (F.comp G)).ofNatIsoRight
      (derivedGraphRestrictionCompositionIso A D E T F G).symm)
end SerrePositivity.DifferentialGraded
