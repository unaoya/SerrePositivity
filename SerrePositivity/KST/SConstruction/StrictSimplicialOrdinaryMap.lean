module
public import SerrePositivity.KST.SConstruction.StrictSimplicialTransformationWhisker

/-! # 全 Hom の作用から通常射と厳密自然性を回収する
概要：厳密単体的豊穣関手の元の通常射を、同じ Hom 同値で取り出す。
方針：単位パラメータの前後合成を元の通常合成と照合する。
規約：全 Hom 作用を保持する。使われ方：実 BF 段比較の通常 dg 射への自然性。
-/
@[expose] public section
noncomputable section
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
variable {C : Type v} {D : Type w} [Category.{u} C] [Category.{u} D]
  [SimplicialCategory C] [SimplicialCategory D]

/-- 同じ元の豊穣 Hom 作用から取り出す通常射。 -/
def strictSimplicialOrdinaryMap (F : EnrichedFunctor SSet.{u} C D)
    {X Y : C} (f : X ⟶ Y) : F.obj X ⟶ F.obj Y :=
  (eHomEquiv SSet).symm (eHomEquiv SSet f ≫ F.map X Y)

/-- 回収した通常射は、同じ豊穣作用の単位パラメータの表示を保つ。 -/
lemma strictSimplicialOrdinaryMap_hom (F : EnrichedFunctor SSet.{u} C D)
    {X Y : C} (f : X ⟶ Y) :
    eHomEquiv SSet (strictSimplicialOrdinaryMap F f) = eHomEquiv SSet f ≫ F.map X Y :=
  Equiv.apply_symm_apply _ _

/-- 豊穣作用で指定した同じ通常射を厳密に回収する。 -/
lemma strictSimplicialOrdinaryMap_of_hom (F : EnrichedFunctor SSet.{u} C D)
    {X Y : C} (f : X ⟶ Y) (g : F.obj X ⟶ F.obj Y)
    (h : eHomEquiv SSet f ≫ F.map X Y = eHomEquiv SSet g) :
    strictSimplicialOrdinaryMap F f = g :=
  (eHomEquiv SSet).injective ((strictSimplicialOrdinaryMap_hom F f).trans h)

/-- 同じ通常射の回収は厳密豊穣関手の後合成と可換。 -/
lemma strictSimplicialOrdinaryMap_comp
    {E : Type z} [Category.{u} E] [SimplicialCategory E]
    (F : EnrichedFunctor SSet.{u} C D) (G : EnrichedFunctor SSet.{u} D E)
    {X Y : C} (f : X ⟶ Y) :
    strictSimplicialOrdinaryMap (F.comp SSet G) f =
      strictSimplicialOrdinaryMap G (strictSimplicialOrdinaryMap F f) := by
  apply (eHomEquiv SSet).injective
  erw [strictSimplicialOrdinaryMap_hom (F.comp SSet G) f,
    strictSimplicialOrdinaryMap_hom G (strictSimplicialOrdinaryMap F f),
    strictSimplicialOrdinaryMap_hom F f]
  exact (Category.assoc _ _ _).symm

/-- 単位パラメータの後合成は元の通常合成を表す。 -/
lemma simplicialHomEquiv_comp_post {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z) :
    eHomEquiv SSet (f ≫ g) = eHomEquiv SSet f ≫ eHomWhiskerLeft SSet X g := by
  rw [eHomEquiv_comp]
  ext n x
  rfl

/-- 単位パラメータの前合成は元の通常合成を表す。 -/
lemma simplicialHomEquiv_comp_pre {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z) :
    eHomEquiv SSet (f ≫ g) = eHomEquiv SSet g ≫ eHomWhiskerRight SSet f Z := by
  rw [eHomEquiv_comp]
  ext n x
  rfl

/-- 全 Hom に関する同じ厳密自然性は、元の通常射に関しても厳密に可換。 -/
lemma strictSimplicialOrdinaryMap_naturality
    (F G : EnrichedFunctor SSet.{u} C D) (τ : ∀ X, F.obj X ⟶ G.obj X)
    (hτ : ∀ X Y, F.map X Y ≫ eHomWhiskerLeft SSet (F.obj X) (τ Y) =
      G.map X Y ≫ eHomWhiskerRight SSet (τ X) (G.obj Y))
    {X Y : C} (f : X ⟶ Y) :
    strictSimplicialOrdinaryMap F f ≫ τ Y = τ X ≫ strictSimplicialOrdinaryMap G f := by
  apply (eHomEquiv SSet).injective
  rw [simplicialHomEquiv_comp_post, simplicialHomEquiv_comp_pre,
    strictSimplicialOrdinaryMap_hom, strictSimplicialOrdinaryMap_hom,
    Category.assoc, Category.assoc, hτ]

end SerrePositivity.KST.SConstruction
