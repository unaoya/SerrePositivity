module
public import SerrePositivity.KST.SConstruction.EnrichedFunctorCollageNerve

/-! # 有向 collage の交差射と上段への比較
概要：元の射 X→RY を collage の交差射として表し、下段 RY→上段 Y の自然変換を構成する。
方針：豊穣単位からの射と通常の射の同値を使い、前後合成を厳密に回収する。
規約：元の豊穣関手 R と元の射の合成を保ち、ホモトピー類への商を取らない。
使われ方：全入力円柱を下段から上段へ合成するための strict な比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
variable {C D : Type v} [Category.{u} C] [Category.{u} D]
  [SimplicialCategory C] [SimplicialCategory D]

/-- 豊穣関手の通常の作用は、単位からの射でも元の写像空間の作用を回収する。 -/
lemma enrichedCollageUnderlying_map_unit (R : EnrichedFunctor SSet.{u} C D)
    {X Y : C} (f : X ⟶ Y) :
    eHomEquiv SSet ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor R).map f) =
      eHomEquiv SSet f ≫ R.map X Y := by
  apply (SSet.unitHomEquiv _).injective
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor_vertex R f

/-- 元の射 X→RY を、下段 X から上段 Y への実際の射として表す。 -/
def enrichedFunctorCollageCross (R : EnrichedFunctor SSet.{u} C D)
    {X : D} {Y : C} (f : X ⟶ R.obj Y) :
    (enrichedFunctorCollageBottom R).obj X ⟶ (enrichedFunctorCollageTop R).obj Y :=
  show 𝟙_ SSet ⟶ SimplicialCategory.sHom X (R.obj Y) from eHomEquiv SSet f

/-- 下段包含の通常の射は、元の射の豊穣単位表示そのもの。 -/
lemma enrichedFunctorCollageBottom_map (R : EnrichedFunctor SSet.{u} C D)
    {X Y : D} (f : X ⟶ Y) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor (enrichedFunctorCollageBottom R)).map f =
      (show 𝟙_ SSet ⟶ SimplicialCategory.sHom X Y from eHomEquiv SSet f) := by
  have h := enrichedCollageUnderlying_map_unit (enrichedFunctorCollageBottom R) f
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor (enrichedFunctorCollageBottom R)).map f =
    eHomEquiv SSet f ≫ 𝟙 _ at h
  exact h.trans (Category.comp_id _)

/-- 上段包含の通常の射も、元の射の豊穣単位表示そのもの。 -/
lemma enrichedFunctorCollageTop_map (R : EnrichedFunctor SSet.{u} C D)
    {X Y : C} (f : X ⟶ Y) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor (enrichedFunctorCollageTop R)).map f =
      (show 𝟙_ SSet ⟶ SimplicialCategory.sHom X Y from eHomEquiv SSet f) := by
  have h := enrichedCollageUnderlying_map_unit (enrichedFunctorCollageTop R) f
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor (enrichedFunctorCollageTop R)).map f =
    eHomEquiv SSet f ≫ 𝟙 _ at h
  exact h.trans (Category.comp_id _)

/-- 交差射の下段での前合成は、元の値域での射の合成を厳密に回収する。 -/
lemma enrichedFunctorCollageCross_pre (R : EnrichedFunctor SSet.{u} C D)
    {X X' : D} {Y : C} (a : X ⟶ X') (f : X' ⟶ R.obj Y) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor (enrichedFunctorCollageBottom R)).map a ≫
        enrichedFunctorCollageCross R f = enrichedFunctorCollageCross R (a ≫ f) := by
  rw [enrichedFunctorCollageBottom_map]
  change (λ_ (𝟙_ SSet)).inv ≫ (eHomEquiv SSet a ⊗ₘ eHomEquiv SSet f) ≫
    eComp SSet X X' (R.obj Y) = eHomEquiv SSet (a ≫ f)
  exact (eHomEquiv_comp SSet a f).symm

/-- 交差射の上段での後合成は、元の R の通常の作用による後合成を厳密に回収する。 -/
lemma enrichedFunctorCollageCross_post (R : EnrichedFunctor SSet.{u} C D)
    {X : D} {Y Z : C} (f : X ⟶ R.obj Y) (b : Y ⟶ Z) :
    enrichedFunctorCollageCross R f ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor (enrichedFunctorCollageTop R)).map b =
      enrichedFunctorCollageCross R (f ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor R).map b) := by
  rw [enrichedFunctorCollageTop_map]
  change (λ_ (𝟙_ SSet)).inv ≫ (eHomEquiv SSet f ⊗ₘ eHomEquiv SSet b) ≫
      (𝟙 (SimplicialCategory.sHom X (R.obj Y)) ⊗ₘ R.map Y Z) ≫
        eComp SSet X (R.obj Y) (R.obj Z) =
    eHomEquiv SSet (f ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor R).map b)
  rw [eHomEquiv_comp]
  let rb : R.obj Y ⟶ R.obj Z := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor R).map b
  change (λ_ (𝟙_ SSet)).inv ≫ (eHomEquiv SSet f ⊗ₘ eHomEquiv SSet b) ≫
      (𝟙 (SimplicialCategory.sHom X (R.obj Y)) ⊗ₘ R.map Y Z) ≫
        eComp SSet X (R.obj Y) (R.obj Z) =
    (λ_ (𝟙_ SSet)).inv ≫ (eHomEquiv SSet f ⊗ₘ eHomEquiv SSet rb) ≫
      eComp SSet X (R.obj Y) (R.obj Z)
  have hr : eHomEquiv SSet rb = eHomEquiv SSet b ≫ R.map Y Z :=
    enrichedCollageUnderlying_map_unit R b
  rw [hr, tensorHom_comp_tensorHom_assoc]
  simp only [Category.comp_id]

/-- 下段 RY から上段 Y への交差恒等射は、上段の全ての射について strict に自然。 -/
def enrichedFunctorCollageComparison (R : EnrichedFunctor SSet.{u} C D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor R ⋙
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor (enrichedFunctorCollageBottom R) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor (enrichedFunctorCollageTop R) where
  app Y := enrichedFunctorCollageCross R (𝟙 (R.obj Y))
  naturality {Y Z} b := by
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor (enrichedFunctorCollageBottom R)).map
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor R).map b) ≫
          enrichedFunctorCollageCross R (𝟙 (R.obj Z)) =
      enrichedFunctorCollageCross R (𝟙 (R.obj Y)) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor (enrichedFunctorCollageTop R)).map b
    rw [enrichedFunctorCollageCross_pre, enrichedFunctorCollageCross_post]
    let rb : R.obj Y ⟶ R.obj Z := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor R).map b
    change enrichedFunctorCollageCross R (rb ≫ 𝟙 (R.obj Z)) =
      enrichedFunctorCollageCross R (𝟙 (R.obj Y) ≫ rb)
    rw [Category.comp_id, Category.id_comp]

end SerrePositivity.KST.SConstruction
