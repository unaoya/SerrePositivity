module
public import SerrePositivity.DifferentialGraded.Morita.ScalarExtensionPerfect
public import SerrePositivity.DifferentialGraded.Morita.PerfectFunctoriality

/-! # U16d：係数変更正方形の実際の主Perf制限と自然性

主導来圏上の指定された係数変更正方形を入力し、実際の非flat係数変更のPerf制限へ移す。
未実装のkernel作用の正方形を証明済みとは仮定しない。kernel固有の入力は明示したまま使う。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory ScalarExtension
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]

def scalarPerfectSquare
    (T : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)
    (T' : DerivedModuleCategory A' (DGBaseChange φ D) ⥤
      DerivedModuleCategory A' (DGBaseChange φ E))
    (hT : ∀ X, modulePerfect A D X → modulePerfect A E (T.obj X))
    (hT' : ∀ X, modulePerfect A' (DGBaseChange φ D) X →
      modulePerfect A' (DGBaseChange φ E) (T'.obj X))
    (e : T ⋙ derivedExtension φ E ≅ derivedExtension φ D ⋙ T') :
    perfectFunctorRestriction A D E T hT ⋙ scalarExtensionPerfectFunctor φ E Set.univ ≅
      scalarExtensionPerfectFunctor φ D Set.univ ⋙
        perfectFunctorRestriction A' (DGBaseChange φ D) (DGBaseChange φ E) T' hT' :=
  NatIso.ofComponents (fun X => (modulePerfect A' (DGBaseChange φ E)).isoMk (e.app X.obj))
    (by intro X Y f
        exact (modulePerfect A' (DGBaseChange φ E)).hom_ext (e.hom.naturality f.hom))

lemma scalarPerfectSquare_inclusion
    (T : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)
    (T' : DerivedModuleCategory A' (DGBaseChange φ D) ⥤
      DerivedModuleCategory A' (DGBaseChange φ E))
    (hT : ∀ X, modulePerfect A D X → modulePerfect A E (T.obj X))
    (hT' : ∀ X, modulePerfect A' (DGBaseChange φ D) X →
      modulePerfect A' (DGBaseChange φ E) (T'.obj X))
    (e : T ⋙ derivedExtension φ E ≅ derivedExtension φ D ⋙ T') :
    Functor.whiskerRight (scalarPerfectSquare φ D E T T' hT hT' e).hom
        (perfectModuleInclusion A' (DGBaseChange φ E) Set.univ) =
      Functor.whiskerLeft (perfectModuleInclusion A D Set.univ) e.hom := rfl

lemma scalarPerfectSquare_naturality
    (T U : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)
    (T' U' : DerivedModuleCategory A' (DGBaseChange φ D) ⥤
      DerivedModuleCategory A' (DGBaseChange φ E))
    (hT : ∀ X, modulePerfect A D X → modulePerfect A E (T.obj X))
    (hU : ∀ X, modulePerfect A D X → modulePerfect A E (U.obj X))
    (hT' : ∀ X, modulePerfect A' (DGBaseChange φ D) X →
      modulePerfect A' (DGBaseChange φ E) (T'.obj X))
    (hU' : ∀ X, modulePerfect A' (DGBaseChange φ D) X →
      modulePerfect A' (DGBaseChange φ E) (U'.obj X))
    (eT : T ⋙ derivedExtension φ E ≅ derivedExtension φ D ⋙ T')
    (eU : U ⋙ derivedExtension φ E ≅ derivedExtension φ D ⋙ U')
    (α : T ⟶ U) (α' : T' ⟶ U')
    (hα : Functor.whiskerRight α (derivedExtension φ E) ≫ eU.hom =
      eT.hom ≫ Functor.whiskerLeft (derivedExtension φ D) α') :
    Functor.whiskerRight (perfectFunctorTransformation A D E T U hT hU α)
        (scalarExtensionPerfectFunctor φ E Set.univ) ≫
        (scalarPerfectSquare φ D E U U' hU hU' eU).hom =
      (scalarPerfectSquare φ D E T T' hT hT' eT).hom ≫
        Functor.whiskerLeft (scalarExtensionPerfectFunctor φ D Set.univ)
          (perfectFunctorTransformation A' (DGBaseChange φ D) (DGBaseChange φ E)
            T' U' hT' hU' α') := by
  apply NatTrans.ext
  funext X
  apply (modulePerfect A' (DGBaseChange φ E)).hom_ext
  exact NatTrans.congr_app hα X.obj

section Composition

variable (B : Type z) [DGCategory A B] [Small.{u} B]
  (T : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)
  (U : DerivedModuleCategory A E ⥤ DerivedModuleCategory A B)
  (T' : DerivedModuleCategory A' (DGBaseChange φ D) ⥤
    DerivedModuleCategory A' (DGBaseChange φ E))
  (U' : DerivedModuleCategory A' (DGBaseChange φ E) ⥤
    DerivedModuleCategory A' (DGBaseChange φ B))
  (hT : ∀ X, modulePerfect A D X → modulePerfect A E (T.obj X))
  (hU : ∀ X, modulePerfect A E X → modulePerfect A B (U.obj X))
  (hT' : ∀ X, modulePerfect A' (DGBaseChange φ D) X →
    modulePerfect A' (DGBaseChange φ E) (T'.obj X))
  (hU' : ∀ X, modulePerfect A' (DGBaseChange φ E) X →
    modulePerfect A' (DGBaseChange φ B) (U'.obj X))
  (eT : T ⋙ derivedExtension φ E ≅ derivedExtension φ D ⋙ T')
  (eU : U ⋙ derivedExtension φ B ≅ derivedExtension φ E ⋙ U')

/-- 二つの主導来係数変更正方形の合成。 -/
def scalarDerivedSquareComposition :
    (T ⋙ U) ⋙ derivedExtension φ B ≅ derivedExtension φ D ⋙ (T' ⋙ U') :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft T eU ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight eT U' ≪≫
    Functor.associator _ _ _

/-- 実際の主Perf制限の合成同型も含めて、二つの係数変更正方形を合成する。 -/
def scalarPerfectSquareComposition :
    perfectFunctorRestriction A D B (T ⋙ U) (fun X h => hU _ (hT X h)) ⋙
        scalarExtensionPerfectFunctor φ B Set.univ ≅
      scalarExtensionPerfectFunctor φ D Set.univ ⋙
        perfectFunctorRestriction A' (DGBaseChange φ D) (DGBaseChange φ B) (T' ⋙ U')
          (fun X h => hU' _ (hT' X h)) :=
  Functor.isoWhiskerRight (perfectFunctorCompositionIso A D E B T U hT hU).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (scalarPerfectSquare φ E B U U' hU hU' eU) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (scalarPerfectSquare φ D E T T' hT hT' eT) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (perfectFunctorCompositionIso A' (DGBaseChange φ D) (DGBaseChange φ E)
        (DGBaseChange φ B) T' U' hT' hU')

/-- 主導来正方形を合成してから制限する経路と、主Perf正方形を合成する経路は一致する。 -/
lemma scalarPerfectSquareComposition_eq :
    scalarPerfectSquare φ D B (T ⋙ U) (T' ⋙ U')
        (fun X h => hU _ (hT X h)) (fun X h => hU' _ (hT' X h))
        (scalarDerivedSquareComposition φ D E B T U T' U' eT eU) =
      scalarPerfectSquareComposition φ D E B T U T' U' hT hU hT' hU' eT eU := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  apply (modulePerfect A' (DGBaseChange φ B)).hom_ext
  simp only [scalarPerfectSquareComposition, scalarPerfectSquare, scalarDerivedSquareComposition,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, perfectFunctorCompositionIso,
    Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, NatIso.ofComponents, ObjectProperty.isoMk,
    Iso.app_hom]
  simp only [Category.id_comp, Category.comp_id]
  change eU.hom.app (T.obj X.obj) ≫ U'.map (eT.hom.app X.obj) =
    (derivedExtension φ B).map (𝟙 _) ≫ eU.hom.app (T.obj X.obj) ≫
      U'.map (eT.hom.app X.obj) ≫ 𝟙 _
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

end Composition

end SerrePositivity.DifferentialGraded.Morita
