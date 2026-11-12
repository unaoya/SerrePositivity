module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentHomotopyVertex
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentTransformationPointEvaluation
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle

/-!
概要：元の関手三角形を同じ三辺・全二単体を持つ coherent な変換三角形にする。
方針：一点パラメータ付き評価を使い、元の三面を厳密に照合する。
規約：元の三角形を選び直さない。使われ方：部分極限比較の二三角形を cospan へ接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 一点パラメータ付きの全評価を底の一点で読むと、元の関手単体の同じ評価。 -/
lemma functorUnitFamilyDiagram_point {B : SSet.{u + 1}} {n : ℕ}
    (T : (Δ[n] : SSet.{u + 1}) ⟶ (ihom B).obj SpaceInfinity.{u}) (b : B _⦋0⦌) :
    coherentTransformationPointDiagram (functorUnitFamilyDiagram T) b =
      T ≫ evaluateFunctorAt b := by
  apply SSet.hom_ext
  intro m
  apply ConcreteCategory.hom_ext
  intro a
  rfl

variable {B : SSet.{u + 1}} {F G J : B ⟶ SpaceInfinity.{u}}
  {l : SSet.Homotopy F G} {r : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle l r d)

/-- 元の三つの円柱を三辺とする、元の二単体の coherent な三角形表示。 -/
def coherentTriangleOfFunctorTriangle : CoherentTransformationVertexTriangle F G J
    (coherentVertexOfHomotopy l) (coherentVertexOfHomotopy r) where
  diagonal := coherentVertexOfHomotopy d
  diagram := functorUnitFamilyDiagram T.diagram
  first := by
    rw [functorUnitFamilyDiagram_pre, T.face_two, coherentVertexOfHomotopy_familyDiagram]
  second := by
    rw [functorUnitFamilyDiagram_pre, T.face_zero, coherentVertexOfHomotopy_familyDiagram]
  long := by
    rw [functorUnitFamilyDiagram_pre, T.face_one, coherentVertexOfHomotopy_familyDiagram]

/-- coherent 表示の対角辺も元の指定円柱の辺そのもの。 -/
lemma coherentTriangleOfFunctorTriangle_diagonal :
    (coherentTriangleOfFunctorTriangle T).diagonal = coherentVertexOfHomotopy d := rfl

/-- 元の coherent 表示の一点評価は、元の関手二単体の同じ点での全評価。 -/
lemma coherentTriangleOfFunctorTriangle_point (b : B _⦋0⦌) :
    coherentTransformationPointDiagram (coherentTriangleOfFunctorTriangle T).diagram b =
      T.diagram ≫ evaluateFunctorAt b := functorUnitFamilyDiagram_point T.diagram b

end SerrePositivity.InfinityCategories.F2
