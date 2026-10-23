module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorTrianglePrismEdges
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorTrianglePointedChoice

/-!
概要：元の指定三角形と全実始域射を固定する、同じ全 pointed 持ち上げの証拠。
方針：元の実延長・全底・初期値を保持し、元の指定三角形の持ち上げも同じ型へ入れる。
規約：任意の全係数を保持。使われ方：零面・固定面を一つの三角形整合式で扱う。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の全三角形・実始域射・全底を保持する pointed な実持ち上げ。 -/
structure FunctorTrianglePointedWitness {B C : SSet.{u + 1}} {F G J : B ⟶ SpaceInfinity.{u}}
    {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {c : SSet.Homotopy F J}
    (T : FunctorCompositionTriangle a b c) (p : C ⟶ B) (s : C ⟶ leftUnstraightening F) where
  prism : (Δ[2] : SSet.{u + 1}) ⊗ C ⟶ PointedSpaceInfinity.{u}
  projection : prism ≫ pointedSpaceProjection = (Δ[2] ◁ p) ≫ functorSimplexDiagram T.diagram
  initial : simplexPrismVertex 2 0 C ≫ prism = s ≫ pullback.fst pointedSpaceProjection F

variable {B C : SSet.{u + 1}} {F G J : B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {c : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b c) (p : C ⟶ B) (s : C ⟶ leftUnstraightening F)

/-- 元の全初期頂点の式は、同じ全初期面を厳密に固定する。 -/
lemma FunctorTrianglePointedWitness.start (w : FunctorTrianglePointedWitness T p s) :
    (scaffoldFirstVertex 2 ▷ C) ≫ w.prism =
      snd Δ[0] C ≫ s ≫ pullback.fst pointedSpaceProjection F := by
  rw [scaffoldFirstVertex_whiskerRight, Category.assoc, w.initial]

/-- 元の指定三角形の同じ持ち上げを、元の全実始域射で制限する。 -/
def functorTrianglePointedCanonicalWitness
    (hi : s ≫ leftUnstraighteningProjection F = p) : FunctorTrianglePointedWitness T p s where
  prism := (Δ[2] ◁ s) ≫ functorTrianglePointedLift T
  projection := by
    rw [Category.assoc, functorTrianglePointedLift_projection, ← Category.assoc,
      ← whiskerLeft_comp, hi]
  initial := by
    have hn : simplexPrismVertex 2 0 C ≫ (Δ[2] ◁ s) =
        s ≫ simplexPrismVertex 2 0 (leftUnstraightening F) := by
      apply SSet.hom_ext
      intro n
      rfl
    rw [← Category.assoc, hn, Category.assoc, functorTrianglePointedLift_initial]

end SerrePositivity.InfinityCategories.F2
