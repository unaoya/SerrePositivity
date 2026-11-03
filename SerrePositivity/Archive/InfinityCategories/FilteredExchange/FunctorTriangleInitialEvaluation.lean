module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorTriangleMiddleEvaluation
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeExtensionUniversalInitial

/-!
概要：元の全三角形比較の第一辺・長辺の始点評価は、元の同じ実始域射へ定値となる。
方針：全延長族の初期面の式を頂点零へ制限し、元の辺の初期頂点と照合する。
規約：全係数と元の全初期値を保持。使われ方：第一辺・長辺の指定比較の簡約。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B C : SSet.{u + 1}} {F G J : B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {c : SSet.Homotopy F J}
  {T : FunctorCompositionTriangle a b c} {p : C ⟶ B} {s : C ⟶ leftUnstraightening F}
  (w : FunctorTrianglePointedWitness T p s)
local notation "base" => (Δ[2] ◁ p) ≫ functorSimplexDiagram T.diagram
local notation "v" => snd Δ[0] C ≫ s ≫ pullback.fst pointedSpaceProjection F
local notation "I" => relativeFunctorExtensionSpaceι pointedSpaceProjection base
  (scaffoldFirstVertex 2 ▷ C) v (FunctorTrianglePointedWitness.start_projection w)

/-- 元の全延長族は、全選択を通じて同じ元の実始域射の初期頂点を保つ。 -/
lemma FunctorTrianglePointedWitness.universal_initial :
    (simplexPrismVertex 2 0 C ▷ w.choice) ≫ relativeFunctorUncurry I =
      fst C w.choice ≫ s ≫ pullback.fst pointedSpaceProjection F := by
  have h₀ := relativeExtensionUniversal_initial pointedSpaceProjection base
    (scaffoldFirstVertex 2 ▷ C) v w.start_projection
  calc
    _ = (simplexPrismVertex 0 0 C ▷ w.choice) ≫
        ((scaffoldFirstVertex 2 ▷ C) ▷ w.choice) ≫ relativeFunctorUncurry I := by
      apply SSet.hom_ext
      intro n
      rfl
    _ = (simplexPrismVertex 0 0 C ▷ w.choice) ≫ fst (Δ[0] ⊗ C) w.choice ≫ v :=
      congrArg (fun k => (simplexPrismVertex 0 0 C ▷ w.choice) ≫ k) h₀
    _ = _ := by
      apply SSet.hom_ext
      intro n
      rfl

/-- 元の初期頂点を含む辺の全始点評価は、元の実始域射の頂点へ定値となる。 -/
lemma FunctorTrianglePointedWitness.edgeSource_constant
    (hi : s ≫ leftUnstraighteningProjection F = p) {Q : B ⟶ SpaceInfinity.{u}}
    (H : SSet.Homotopy F Q) (i : Fin 3) (hFace : stdSimplex.δ i ≫ T.diagram = curry H.h)
    (hStart : prismEndpoint 0 C ≫ (stdSimplex.δ i ▷ C) = simplexPrismVertex 2 0 C) :
    w.edgeMap H i hFace ≫ functorHomotopyPrismSourceEvaluation H p =
      (SSet.const (relativeFunctorVertex (leftUnstraighteningProjection F) p s hi) : w.choice ⟶
        _) := by
  apply relativeFunctorUncurry_injective
  apply pullback.hom_ext
  · rw [functorHomotopyPrismSourceEvaluation, relativeFunctorRestrictedEndpoint_uncurry,
      w.edgeMap_uncurry H i hFace, ← Category.assoc, ← comp_whiskerRight, hStart,
      w.universal_initial]
    change (fst C w.choice ≫ s ≫ pullback.fst pointedSpaceProjection F) =
      uncurry (SSet.const (functorVertex s)) ≫ pullback.fst pointedSpaceProjection F
    rw [uncurry_const_functorVertex, Category.assoc]
  · exact (relativeFunctorUncurry_projection _).trans (relativeFunctorUncurry_projection _).symm

/-- 元の第一辺の全始点評価は、元の同じ実始域射に定値。 -/
lemma FunctorTrianglePointedWitness.firstSource_constant
    (hi : s ≫ leftUnstraighteningProjection F = p) :
    w.edgeMap a 2 T.face_two ≫ functorHomotopyPrismSourceEvaluation a p =
      (SSet.const (relativeFunctorVertex (leftUnstraighteningProjection F) p s hi) : w.choice ⟶
        _) :=
  w.edgeSource_constant hi a 2 T.face_two (by apply SSet.hom_ext; intro n; rfl)

/-- 元の長辺の全始点評価も、元の同じ実始域射に定値。 -/
lemma FunctorTrianglePointedWitness.longSource_constant
    (hi : s ≫ leftUnstraighteningProjection F = p) :
    w.edgeMap c 1 T.face_one ≫ functorHomotopyPrismSourceEvaluation c p =
      (SSet.const (relativeFunctorVertex (leftUnstraighteningProjection F) p s hi) : w.choice ⟶
        _) :=
  w.edgeSource_constant hi c 1 T.face_one (by apply SSet.hom_ext; intro n; rfl)

end SerrePositivity.InfinityCategories.F2
