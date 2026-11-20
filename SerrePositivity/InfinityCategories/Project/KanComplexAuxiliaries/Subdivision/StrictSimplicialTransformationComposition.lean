module

public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.StrictSimplicialTransformation

/-! # 厳密単体的自然変換の同じ全 Hom 上の合成
概要：単位次数の全族を元の豊穣合成で合成し、全パラメータ自然性を保つ。
方針：全単体で豊穣結合律と二つの自然性を順に適用する。
規約：成分だけの合成には留めない。使われ方：Ex∞ 比較と元の組み立ての右脚。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet

/-- 元の豊穣合成の結合律は、全次数の元の三つの単体で成り立つ。 -/
lemma simplicialComposition_assoc_app {D : Type w} [EnrichedCategory SSet.{u} D]
    (W X Y Z : D) (n : SimplexCategoryᵒᵖ)
    (f : (W ⟶[SSet.{u}] X).obj n) (g : (X ⟶[SSet.{u}] Y).obj n)
    (h : (Y ⟶[SSet.{u}] Z).obj n) :
    (eComp SSet W Y Z).app n ((eComp SSet W X Y).app n (f, g), h) =
      (eComp SSet W X Z).app n (f, (eComp SSet X Y Z).app n (g, h)) :=
  types_congr_hom (NatTrans.congr_app (e_assoc SSet W X Y Z) n) (f, (g, h))

/-- 二つの厳密単体的自然変換を、同じ単位パラメータと豊穣合成で合成する。 -/
def strictSimplicialTransformationComp
    {C : Type v} {D : Type w} [EnrichedCategory SSet.{u} C]
    [EnrichedCategory SSet.{u} D] (F G H : EnrichedFunctor SSet.{u} C D)
    (η : GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u})) F G)
    (θ : GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u})) G H) :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u})) F H where
  app X := (λ_ (𝟙_ SSet.{u})).inv ≫ (η.app X ⊗ₘ θ.app X) ≫ eComp SSet _ _ _
  naturality X Y := by
    ext n t
    have hη := types_congr_hom (NatTrans.congr_app (η.naturality X Y) n) t
    have hθ := types_congr_hom (NatTrans.congr_app (θ.naturality X Y) n) t
    change (eComp SSet (F.obj X) (F.obj Y) (G.obj Y)).app n
      ((F.map X Y).app n t.2, (η.app Y).app n t.1) =
      (eComp SSet (F.obj X) (G.obj X) (G.obj Y)).app n
        ((η.app X).app n t.1, (G.map X Y).app n t.2) at hη
    change (eComp SSet (G.obj X) (G.obj Y) (H.obj Y)).app n
      ((G.map X Y).app n t.2, (θ.app Y).app n t.1) =
      (eComp SSet (G.obj X) (H.obj X) (H.obj Y)).app n
        ((θ.app X).app n t.1, (H.map X Y).app n t.2) at hθ
    change (eComp SSet (F.obj X) (F.obj Y) (H.obj Y)).app n
      ((F.map X Y).app n t.2, (eComp SSet (F.obj Y) (G.obj Y) (H.obj Y)).app n
        ((η.app Y).app n t.1, (θ.app Y).app n t.1)) =
      (eComp SSet (F.obj X) (H.obj X) (H.obj Y)).app n
        ((eComp SSet (F.obj X) (G.obj X) (H.obj X)).app n
          ((η.app X).app n t.1, (θ.app X).app n t.1), (H.map X Y).app n t.2)
    rw [← _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.simplicialComposition_assoc_app, hη, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.simplicialComposition_assoc_app, hθ,
      ← _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.simplicialComposition_assoc_app]

/-- 成分が元の通常射を回収する二つの比較の合成は、同じ通常の合成射を回収する。 -/
lemma strictSimplicialTransformationComp_hom
    {C : Type v} {D : Type w} [EnrichedCategory SSet.{u} C]
    [Category.{u} D] [SimplicialCategory D] (F G H : EnrichedFunctor SSet.{u} C D)
    (η : GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u})) F G)
    (θ : GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u})) G H)
    (X : C) (f : F.obj X ⟶ G.obj X) (g : G.obj X ⟶ H.obj X)
    (hf : η.app X = eHomEquiv SSet f) (hg : θ.app X = eHomEquiv SSet g) :
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialTransformationComp F G H η θ).app X = eHomEquiv SSet (f ≫ g) := by
  change (λ_ (𝟙_ SSet.{u})).inv ≫ (η.app X ⊗ₘ θ.app X) ≫ eComp SSet _ _ _ = _
  rw [hf, hg]
  exact (eHomEquiv_comp SSet f g).symm

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
