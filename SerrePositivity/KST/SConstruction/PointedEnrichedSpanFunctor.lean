module
public import SerrePositivity.KST.SConstruction.PointedSpanEnrichment

/-! # 二つの厳密自然な脚から実 span 図式値の豊穣関手へ
概要：元の三つの値と二つの全 Hom に自然な脚を、span 図式全体の標準 end に束ねる。
方針：全パラメータ作用を end へ持ち上げ、射影で元の単位・合成を検出する。
規約：三頂点の写像だけの直積ではない。使われ方：関手的 BF の enriched span 入力。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Limits SSet
variable {C : Type v} [EnrichedCategory SSet.{u} C]
  (F L R : EnrichedFunctor SSet.{u} C PointedSSetObject.{u})
  (l : ∀ X, F.obj X ⟶ L.obj X) (r : ∀ X, F.obj X ⟶ R.obj X)
  (hl : ∀ X Y, F.map X Y ≫ eHomWhiskerLeft SSet (F.obj X) (l Y) =
    L.map X Y ≫ eHomWhiskerRight SSet (l X) (L.obj Y))
  (hr : ∀ X Y, F.map X Y ≫ eHomWhiskerLeft SSet (F.obj X) (r Y) =
    R.map X Y ≫ eHomWhiskerRight SSet (r X) (R.obj Y))

/-- 元の三つの値と二つの同じ脚からなる、実際の span 図式。 -/
def pointedEnrichedSpanValue (X : C) : WalkingSpan ⥤ PointedSSetObject.{u} :=
  span (l X) (r X)

/-- 三頂点の同じ全パラメータ作用。 -/
def pointedEnrichedSpanComponentMap (X Y : C) :
    ∀ i : WalkingSpan, (X ⟶[SSet.{u}] Y) ⟶
      ((pointedEnrichedSpanValue F L R l r X).obj i ⟶[SSet.{u}]
        (pointedEnrichedSpanValue F L R l r Y).obj i)
  | WalkingSpan.zero => F.map X Y
  | WalkingSpan.left => L.map X Y
  | WalkingSpan.right => R.map X Y

/-- 二つの元の矢に自然な全作用を、図式全体の標準 end の Hom へ持ち上げる。 -/
def pointedEnrichedSpanHom (X Y : C) :
    (X ⟶[SSet.{u}] Y) ⟶ Enriched.FunctorCategory.enrichedHom SSet
      (pointedEnrichedSpanValue F L R l r X) (pointedEnrichedSpanValue F L R l r Y) :=
  end_.lift (F := Enriched.FunctorCategory.diagram SSet
    (pointedEnrichedSpanValue F L R l r X) (pointedEnrichedSpanValue F L R l r Y))
    (pointedEnrichedSpanComponentMap F L R l r X Y) (by
    intro i j f
    change pointedEnrichedSpanComponentMap F L R l r X Y i ≫
      eHomWhiskerLeft SSet ((pointedEnrichedSpanValue F L R l r X).obj i)
        ((pointedEnrichedSpanValue F L R l r Y).map f) =
      pointedEnrichedSpanComponentMap F L R l r X Y j ≫
        eHomWhiskerRight SSet ((pointedEnrichedSpanValue F L R l r X).map f)
          ((pointedEnrichedSpanValue F L R l r Y).obj j)
    cases f using WidePushoutShape.Hom.rec with
    | id i =>
      change _ ≫ eHomWhiskerLeft SSet _ (𝟙 _) = _ ≫ eHomWhiskerRight SSet (𝟙 _) _
      rw [eHomWhiskerLeft_id, eHomWhiskerRight_id]
    | init j => cases j with
      | left => exact hl X Y
      | right => exact hr X Y)

/-- 標準 end への持ち上げは、各頂点の同じ元の全作用を厳密に回収する。 -/
lemma pointedEnrichedSpanHom_projection (X Y : C) (i : WalkingSpan) :
    pointedEnrichedSpanHom F L R l r hl hr X Y ≫
      Enriched.FunctorCategory.enrichedHomπ SSet
        (pointedEnrichedSpanValue F L R l r X) (pointedEnrichedSpanValue F L R l r Y) i =
      pointedEnrichedSpanComponentMap F L R l r X Y i := end_.lift_π _ _ _

/-- 元の三つの全作用と二つの脚を保つ、実 span 図式値の厳密豊穣関手。 -/
def pointedEnrichedSpanFunctor : EnrichedFunctor SSet.{u} C PointedSpanDiagram.{u} where
  obj X := ⟨pointedEnrichedSpanValue F L R l r X⟩
  map := pointedEnrichedSpanHom F L R l r hl hr
  map_id X := by
    apply end_.hom_ext
    intro i
    erw [Category.assoc, pointedEnrichedSpanHom_projection,
      Enriched.FunctorCategory.enrichedId_π]
    cases i with
    | none => exact F.map_id X
    | some j => cases j with
      | left => exact L.map_id X
      | right => exact R.map_id X
  map_comp X Y Z := by
    apply end_.hom_ext
    intro i
    erw [Category.assoc, pointedEnrichedSpanHom_projection, Category.assoc,
      Enriched.FunctorCategory.enrichedComp_π]
    erw [← Category.assoc, tensorHom_comp_tensorHom]
    erw [pointedEnrichedSpanHom_projection, pointedEnrichedSpanHom_projection]
    cases i with
    | none => exact F.map_comp X Y Z
    | some j => cases j with
      | left => exact L.map_comp X Y Z
      | right => exact R.map_comp X Y Z

end SerrePositivity.KST.SConstruction
