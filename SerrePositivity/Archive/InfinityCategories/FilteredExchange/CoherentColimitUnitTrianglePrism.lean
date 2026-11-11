module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoconeUnitFamilyConstant
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle

/-!
概要：元の関手二単体から余極限側の同じ二単体への単位の全三角柱。
方針：全単位族を元の二単体へ制限し、両端と三つの側面を厳密に回収する。
規約：元の三辺・全二単体・単位正方形を保持。使われ方：三比較の指定 path の整合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {l : SSet.Homotopy F G} {r : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle l r d)

/-- 元の全関手二単体を、同じ余極限単位で動かす全三角柱。 -/
def coherentColimitUnitTrianglePrism : (Δ[2] : SSet.{u + 1}) ⊗ Δ[1] ⟶
    (ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u} :=
  (T.diagram ▷ Δ[1]) ≫ coherentColimitUnitFamily B

/-- 時間零の全二単体は元の入力三角形そのもの。 -/
lemma coherentColimitUnitTrianglePrism_zero :
    SSet.ι₀ ≫ coherentColimitUnitTrianglePrism B T = T.diagram := by
  rw [coherentColimitUnitTrianglePrism, ← Category.assoc, SSet.ι₀_comp, Category.assoc]
  change T.diagram ≫ (SSet.ι₀ ≫ coconeUnitFamily (coherentColimitCoconeFunctor B)) = _
  rw [coconeUnitFamily_zero, coherentColimitCoconeFunctor_restrict, Category.comp_id]

/-- 時間一では元の余極限関手が送る全二単体を、底に関して定値にした族。 -/
lemma coherentColimitUnitTrianglePrism_one :
    SSet.ι₁ ≫ coherentColimitUnitTrianglePrism B T =
      T.diagram ≫ coherentColimitFunctor B ≫
        constantDiagram ((SSet.uliftFunctor.{u + 1, u}).obj B) SpaceInfinity.{u} := by
  rw [coherentColimitUnitTrianglePrism, ← Category.assoc, SSet.ι₁_comp, Category.assoc]
  change T.diagram ≫ (SSet.ι₁ ≫ coconeUnitFamily (coherentColimitCoconeFunctor B)) = _
  rw [coconeUnitFamily_one_constant]
  rfl

/-- 最初の側面は、元の最初の辺の単位正方形の座標順だけを交換したもの。 -/
lemma coherentColimitUnitTrianglePrism_first :
    (stdSimplex.δ (2 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫
      coherentColimitUnitTrianglePrism B T =
        (β_ Δ[1] Δ[1]).hom ≫ coherentColimitUnitSquare B l := by
  rw [coherentColimitUnitTrianglePrism, ← Category.assoc, ← comp_whiskerRight,
    T.face_two, coherentColimitUnitFamily_edge]

/-- 最後の側面も、元の最後の辺の同じ全単位正方形。 -/
lemma coherentColimitUnitTrianglePrism_last :
    (stdSimplex.δ (0 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫
      coherentColimitUnitTrianglePrism B T =
        (β_ Δ[1] Δ[1]).hom ≫ coherentColimitUnitSquare B r := by
  rw [coherentColimitUnitTrianglePrism, ← Category.assoc, ← comp_whiskerRight,
    T.face_zero, coherentColimitUnitFamily_edge]

/-- 長辺の側面も、元の共通対角辺の全単位正方形。 -/
lemma coherentColimitUnitTrianglePrism_long :
    (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫
      coherentColimitUnitTrianglePrism B T =
        (β_ Δ[1] Δ[1]).hom ≫ coherentColimitUnitSquare B d := by
  rw [coherentColimitUnitTrianglePrism, ← Category.assoc, ← comp_whiskerRight,
    T.face_one, coherentColimitUnitFamily_edge]

end SerrePositivity.InfinityCategories.F2
