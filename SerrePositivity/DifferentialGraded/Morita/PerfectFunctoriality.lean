module
public import SerrePositivity.DifferentialGraded.Perfect.UniversalProperty

/-! # U16d：主Perfへの実際の制限の関手性

kernel作用を主Perfへ制限する際のアダプタ。保存条件を明示し、未実装のkernel作用を仮定しない。
通常の完全充満部分圏のliftを再利用して、射・自然変換・合成の比較を保持する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]

lemma perfectFunctor_of_generators (T : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)
    [T.CommShift ℤ] [T.IsTriangulated]
    (hgen : ∀ d : D, modulePerfect A E (T.obj ((moduleToDerived A D).obj
      (ForgetEnrichment.of (Complex A) (representable A d)))))
    {X : DerivedModuleCategory A D} (hX : modulePerfect A D X) :
    modulePerfect A E (T.obj X) := by
  let P := (modulePerfect A E).inverseImage T
  have : P.IsTriangulated := by dsimp [P]; infer_instance
  have : P.IsClosedUnderIsomorphisms := by dsimp [P]; infer_instance
  have : P.IsStableUnderRetracts :=
    ⟨fun r hY => (modulePerfect A E).prop_of_retract (r.map T) hY⟩
  exact ((modulePerfect_le_iff_generators A D P).2 hgen) X hX

def perfectFunctorRestriction (T : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)
    (hT : ∀ X, modulePerfect A D X → modulePerfect A E (T.obj X)) :
    PerfectModuleCategory A D ⥤ PerfectModuleCategory A E :=
  (modulePerfect A E).lift (perfectModuleInclusion A D Set.univ ⋙ T)
    (fun X => hT X.obj X.property)

def perfectFunctorInclusionIso (T : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)
    (hT : ∀ X, modulePerfect A D X → modulePerfect A E (T.obj X)) :
    perfectFunctorRestriction A D E T hT ⋙ perfectModuleInclusion A E Set.univ ≅
      perfectModuleInclusion A D Set.univ ⋙ T := Iso.refl _

def perfectFunctorTransformation
    (T U : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)
    (hT : ∀ X, modulePerfect A D X → modulePerfect A E (T.obj X))
    (hU : ∀ X, modulePerfect A D X → modulePerfect A E (U.obj X)) (α : T ⟶ U) :
    perfectFunctorRestriction A D E T hT ⟶ perfectFunctorRestriction A D E U hU where
  app X := ObjectProperty.homMk (α.app X.obj)
  naturality _ _ f := (modulePerfect A E).hom_ext (α.naturality f.hom)

lemma perfectFunctorTransformation_id
    (T : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)
    (hT : ∀ X, modulePerfect A D X → modulePerfect A E (T.obj X)) :
    perfectFunctorTransformation A D E T T hT hT (𝟙 T) = 𝟙 _ := rfl

lemma perfectFunctorTransformation_comp
    (T U V : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)
    (hT : ∀ X, modulePerfect A D X → modulePerfect A E (T.obj X))
    (hU : ∀ X, modulePerfect A D X → modulePerfect A E (U.obj X))
    (hV : ∀ X, modulePerfect A D X → modulePerfect A E (V.obj X))
    (α : T ⟶ U) (β : U ⟶ V) :
    perfectFunctorTransformation A D E T V hT hV (α ≫ β) =
      perfectFunctorTransformation A D E T U hT hU α ≫
        perfectFunctorTransformation A D E U V hU hV β := rfl

def perfectFunctorIso
    (T U : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)
    (hT : ∀ X, modulePerfect A D X → modulePerfect A E (T.obj X))
    (hU : ∀ X, modulePerfect A D X → modulePerfect A E (U.obj X)) (e : T ≅ U) :
    perfectFunctorRestriction A D E T hT ≅ perfectFunctorRestriction A D E U hU :=
  NatIso.ofComponents (fun X => (modulePerfect A E).isoMk (e.app X.obj))
    (by intro X Y f; exact (modulePerfect A E).hom_ext (e.hom.naturality f.hom))

def perfectFunctorIdentityIso :
    perfectFunctorRestriction A D D (𝟭 _) (fun _ h => h) ≅ 𝟭 (PerfectModuleCategory A D) :=
  Iso.refl _

variable (B : Type z) [DGCategory A B] [Small.{u} B]

def perfectFunctorCompositionIso
    (T : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)
    (U : DerivedModuleCategory A E ⥤ DerivedModuleCategory A B)
    (hT : ∀ X, modulePerfect A D X → modulePerfect A E (T.obj X))
    (hU : ∀ X, modulePerfect A E X → modulePerfect A B (U.obj X)) :
    perfectFunctorRestriction A D E T hT ⋙ perfectFunctorRestriction A E B U hU ≅
      perfectFunctorRestriction A D B (T ⋙ U) (fun X h => hU _ (hT X h)) := Iso.refl _

lemma perfectFunctorComposition_naturality
    (T T' : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)
    (U U' : DerivedModuleCategory A E ⥤ DerivedModuleCategory A B)
    (hT : ∀ X, modulePerfect A D X → modulePerfect A E (T.obj X))
    (hT' : ∀ X, modulePerfect A D X → modulePerfect A E (T'.obj X))
    (hU : ∀ X, modulePerfect A E X → modulePerfect A B (U.obj X))
    (hU' : ∀ X, modulePerfect A E X → modulePerfect A B (U'.obj X))
    (α : T ⟶ T') (β : U ⟶ U') :
    NatTrans.hcomp (perfectFunctorTransformation A D E T T' hT hT' α)
        (perfectFunctorTransformation A E B U U' hU hU' β) ≫
        (perfectFunctorCompositionIso A D E B T' U' hT' hU').hom =
      (perfectFunctorCompositionIso A D E B T U hT hU).hom ≫
        perfectFunctorTransformation A D B (T ⋙ U) (T' ⋙ U')
          (fun X h => hU _ (hT X h)) (fun X h => hU' _ (hT' X h)) (NatTrans.hcomp α β) := by
  simp only [perfectFunctorCompositionIso, Iso.refl_hom, Category.comp_id, Category.id_comp]
  apply NatTrans.ext
  funext X
  apply (modulePerfect A B).hom_ext
  simp only [NatTrans.hcomp_app]
  change β.app (T.obj X.obj) ≫ U'.map (α.app X.obj) = (NatTrans.hcomp α β).app X.obj
  exact (NatTrans.hcomp_app α β X.obj).symm

end SerrePositivity.DifferentialGraded.Morita
