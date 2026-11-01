module
public import SerrePositivity.InfinityCategories.Kan.StrictSimplicialOrdinaryMap

/-! # 同じ厳密単体的豊穣関手の通常の関手
概要：全 Hom を持つ豊穣関手から、同じ対象・通常射を持つ関手を取り出す。
方針：通常豊穣と基礎圏の標準同値を、元の豊穣関手の両側に合成する。
規約：射の回収に使う同値は元の eHomEquiv。使われ方：実 BF K の整数群関手。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
variable {C : Type v} {D : Type w} [Category.{u} C] [Category.{u} D]
  [SimplicialCategory C] [SimplicialCategory D]

/-- 同じ豊穣作用から回収した通常射を持つ、元の対象間の通常の関手。 -/
def strictSimplicialOrdinaryFunctor (F : EnrichedFunctor SSet.{u} C D) : C ⥤ D :=
  ForgetEnrichment.equivInverse SSet C ⋙ F.forget ⋙ ForgetEnrichment.equivFunctor SSet D

/-- 基礎圏へ取り出した通常射は、元の全 Hom 作用からの射そのもの。 -/
lemma strictSimplicialOrdinaryFunctor_map (F : EnrichedFunctor SSet.{u} C D)
    {X Y : C} (f : X ⟶ Y) :
    (strictSimplicialOrdinaryFunctor F).map f = strictSimplicialOrdinaryMap F f := rfl

end SerrePositivity.KST.SConstruction
