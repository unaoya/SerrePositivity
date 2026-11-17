module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.SourceHom
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeHammockPrecompose

/-!
# 点による豊穣前合成と同じ Kan 単位

概要：HA 3.2.4.7 の指定脚の前合成を、実際の Kan 化された Hom の作用へ照合する。
方針：豊穣関手の合成則と同じ Ex∞ 単位の自然性を使う。
規約：π₀ の式だけでなく、全単体の射を局所化して比較する。
使われ方：native な余積錐の Hom の検査。［一般∞］の移動候補。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.EInfinity
open CategoryTheory MonoidalCategory EnrichedCategory
open _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization SerrePositivity.SimplicialModel

/-- 単位からの点を左に合成する実際の豊穣 Hom の射。 -/
def enrichedPointPrecompose {C : Type v} [EnrichedCategory SSet.{u} C]
    {X Y : C} (p : 𝟙_ SSet.{u} ⟶ X ⟶[SSet.{u}] Y) (Z : C) :
    (Y ⟶[SSet.{u}] Z) ⟶ X ⟶[SSet.{u}] Z :=
  (λ_ _).inv ≫ p ▷ _ ≫ eComp SSet.{u} X Y Z

/-- 指定した点での前合成は、豊穣関手の Hom の比較と全単体で可換。 -/
lemma enrichedPointPrecompose_naturality {C : Type v} [EnrichedCategory SSet.{u} C]
    {D : Type w} [EnrichedCategory SSet.{u} D] (F : EnrichedFunctor SSet.{u} C D)
    {X Y : C} (p : 𝟙_ SSet.{u} ⟶ X ⟶[SSet.{u}] Y) (Z : C) :
    F.map Y Z ≫ enrichedPointPrecompose (p ≫ F.map X Y) (F.obj Z) =
      enrichedPointPrecompose p Z ≫ F.map X Z := by
  simp only [enrichedPointPrecompose, Category.assoc, F.map_comp,
    leftUnitor_inv_naturality_assoc, comp_whiskerRight, tensorHom_def,
    whisker_exchange_assoc]

/-- 反対圏での後合成は、元の圏での同じ射の前合成である。 -/
lemma simplicialHomWhiskerLeft_op {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} (f : X ⟶ Y) (Z : C) :
    eHomWhiskerLeft SSet.{u} (Opposite.op Z) f.op = eHomWhiskerRight SSet.{u} f Z := by
  simp only [eHomWhiskerLeft, eHomWhiskerRight, eComp_op_eq]
  change (ρ_ _).inv ≫ _ ◁ eHomEquiv SSet.{u} f ≫ (β_ _ _).hom ≫ _ = _
  rw [BraidedCategory.braiding_naturality_right_assoc,
    CategoryTheory.rightUnitor_inv_braiding_assoc]
  rfl

/-- 指定された厳密射の実際の Kan Hom への前合成。 -/
def kanStrictPrecompose (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) {X Y : C.category}
    (f : X ⟶ Y) (Z : C.category) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHom C Y Z) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHom C X Z) :=
  enrichedPointPrecompose (C := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanLocalizationObjects C)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationArrowPoint C f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app _) Z

/-- 実際の前合成と、元の前合成の Ex∞ 像は同じ局所化された射。 -/
lemma kanStrictPrecompose_localized (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) {X Y : C.category}
    (f : X ⟶ Y) (Z : C.category) :
    AnodyneHomotopy.anodyneQ.map (kanStrictPrecompose C f Z) =
      AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationPrecompose C Z f)) := by
  let Q := AnodyneHomotopy.anodyneQ
  have := SSet.anodyneExtensions.Q_inverts
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHom C Y Z)) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHomKanUnit_anodyne C Y Z)
  apply (cancel_epi (Q.map (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHom C Y Z)))).mp
  rw [← Q.map_comp, ← Q.map_comp]
  apply congrArg Q.map
  have hn := enrichedPointPrecompose_naturality (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanLocalizationUnit C)
    (X := (show _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.LocalizationObjects C from X)) (Y := (show _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.LocalizationObjects C from Y))
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationArrowPoint C f) (show _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.LocalizationObjects C from Z)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHom C Y Z) ≫ kanStrictPrecompose C f Z =
    ((λ_ (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHom C Y Z)).inv ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationArrowPoint C f ▷ _ ≫
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationComposition C X Y Z) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHom C X Z) at hn
  exact hn.trans (by
    simpa only [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationPrecompose, tensorHom_def, MonoidalCategory.whiskerLeft_id,
      Category.comp_id, Functor.id_map] using
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.naturality (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationPrecompose C Z f)))

end SerrePositivity.EInfinity
