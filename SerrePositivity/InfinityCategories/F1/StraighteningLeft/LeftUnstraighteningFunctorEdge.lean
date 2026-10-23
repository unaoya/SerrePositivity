module

public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FunctorPrismTriangles
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraighteningComposition
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraighteningIdentity

/-!
概要：関手単体集合の辺に対する unstraightening の射と恒等・合成則。
方針：辺と三角形の prism 表示を使い、具体的な変換の持ち上げの比較を適用する。
規約：同型は底を保つ相対関手空間内で取る。
使われ方：Kerodon Corollary 5.6.0.6、一般の coherent な図式の変換への作用。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：coherent な図式間の関手空間の辺に unstraightening 間の底上の射を対応させる。
方針：辺の prism 表示に変換の持ち上げの選択を適用する。
規約：底 B は任意の単体集合。
使われ方：Kerodon Corollary 5.6.0.6、関手空間の辺での unstraightening。 -/
noncomputable def leftUnstraighteningEdgeMap {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u})
    (e : SSet.Edge (X := (ihom B).obj SpaceInfinity.{u}) (functorVertex F) (functorVertex G)) :
    {f : leftUnstraightening F ⟶ leftUnstraightening G //
      f ≫ leftUnstraighteningProjection G = leftUnstraighteningProjection F} :=
  leftUnstraighteningTransformationMap F G (functorEdgePrism e)
    (functorEdgePrism_zero e) (functorEdgePrism_one e)

/-- 概要：関手空間の恒等辺の unstraightening は底上の写像空間で恒等射と同型。
方針：恒等辺の prism が定値の族であることと、定値変換の単位則を使う。
規約：選択した通常の射の厳密な恒等性は要求しない。
使われ方：Kerodon Corollary 5.6.0.6、関手空間での unstraightening の単位則。 -/
noncomputable def leftUnstraighteningEdgeMap_identityIso {B : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) :
    VertexIso (relativeFunctorVertex (leftUnstraighteningProjection F)
      (leftUnstraighteningProjection F)
      (leftUnstraighteningEdgeMap F F (SSet.Edge.id (functorVertex F))).val
      (leftUnstraighteningEdgeMap F F (SSet.Edge.id (functorVertex F))).property)
      (relativeFunctorVertex (leftUnstraighteningProjection F) (leftUnstraighteningProjection F)
        (𝟙 _) (Category.id_comp _)) := by
  have h : functorEdgePrism (F := F) (G := F)
      (SSet.Edge.id (X := (ihom B).obj SpaceInfinity.{u}) (functorVertex F)) =
        CartesianMonoidalCategory.snd (Δ[1] : SSet.{u + 1}) B ≫ F := functorEdgePrism_id F
  simpa only [leftUnstraighteningEdgeMap, h, leftUnstraighteningIdentityTransformation] using
    leftUnstraighteningTransformationMap_identityIso F

/-- 概要：関手空間の合成三角形の長辺の unstraightening は二辺の射の合成と底上で同型。
方針：三角形の prism の三つの辺を計算し、変換の合成則へ適用する。
規約：底 B の quasicategory 性は不要。
使われ方：Kerodon Corollary 5.6.0.6、関手空間での unstraightening の合成則。 -/
noncomputable def leftUnstraighteningEdgeMap_compositionIso {B : SSet.{u + 1}}
    {F G J : B ⟶ SpaceInfinity.{u}}
    {e : SSet.Edge (X := (ihom B).obj SpaceInfinity.{u}) (functorVertex F) (functorVertex G)}
    {f : SSet.Edge (X := (ihom B).obj SpaceInfinity.{u}) (functorVertex G) (functorVertex J)}
    {g : SSet.Edge (X := (ihom B).obj SpaceInfinity.{u}) (functorVertex F) (functorVertex J)}
    (σ : SSet.Edge.CompStruct e f g) :
    VertexIso (relativeFunctorVertex (leftUnstraighteningProjection J)
      (leftUnstraighteningProjection F) (leftUnstraighteningEdgeMap F J g).val
        (leftUnstraighteningEdgeMap F J g).property)
      (relativeFunctorVertex (leftUnstraighteningProjection J) (leftUnstraighteningProjection F)
        ((leftUnstraighteningEdgeMap F G e).val ≫ (leftUnstraighteningEdgeMap G J f).val) (by
          rw [Category.assoc, (leftUnstraighteningEdgeMap G J f).property,
            (leftUnstraighteningEdgeMap F G e).property])) :=
  leftUnstraighteningTransformationMap_compositionIso F G J
    (functorEdgePrism e) (functorEdgePrism f) (functorEdgePrism g)
    (functorEdgePrism_zero e) (functorEdgePrism_one e)
    (functorEdgePrism_zero f) (functorEdgePrism_one f)
    (functorEdgePrism_zero g) (functorEdgePrism_one g)
    (functorFamilyPrism (SSet.yonedaEquiv.symm σ.simplex))
    (functorCompStructPrism_two σ) (functorCompStructPrism_zero σ) (functorCompStructPrism_one σ)

end SerrePositivity.InfinityCategories
