module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.HomFixedComponent
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalFunctorHomPrismCurry

/-!
概要：分類先の実際の固定成分 fiber の族を、三辺を固定した prism に展開する。
方針：元の関手圏の Hom の展開と、同じ評価 fiber の定値条件を使う。
規約：対象の図式、成分の頂点と全パラメーターを保持する。
使われ方：一次元の分類先の fiber を、二つの実際の三角形へ分解する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 元の分類図式の底を、Cat∞ と同じ宇宙で固定する。 -/
abbrev cocartesianHomDiagramBase (C : Type u) [Category.{u} C] : SSet.{u + 1} :=
  (SSet.uliftFunctor.{u + 1, u}).obj (nerve C)

variable {C : Type u} [Category.{u} C] (F G : CocartesianTransportDiagramCategory C) (c : C)
variable (v : (intervalMappingSpace (coherentNerveVertex (cocartesianTransportDiagramValue F c))
  (coherentNerveVertex (cocartesianTransportDiagramValue G c))) _⦋0⦌)
local notation "B" => (cocartesianHomDiagramBase C)
local notation "D₀" => (qCatDiagramCoherentNerve (cocartesianTransportDiagramValueFunctor F))
local notation "D₁" => (qCatDiagramCoherentNerve (cocartesianTransportDiagramValueFunctor G))
local notation "p" => (cocartesianHomIntervalEvaluation F G c)
local notation "E" => (vertexFiber p v)

/-- 元の固定成分 fiber の全パラメーターの族を、底全体で評価する prism。 -/
def cocartesianHomFixedComponentPrism {T : SSet.{u + 1}} (f : T ⟶ E) :
    ((Δ[1] : SSet.{u + 1}) ⊗ B) ⊗ T ⟶ CatInfinity.{u} :=
  intervalFunctorHomPrism (f ≫ vertexFiberι p v)

/-- 同じ固定成分 prism の最初の辺は、元の始域図式。 -/
lemma cocartesianHomFixedComponentPrism_zero {T : SSet.{u + 1}} (f : T ⟶ E) :
    (prismEndpoint 0 B ▷ T) ≫ cocartesianHomFixedComponentPrism F G c v f =
      fst B T ≫ D₀ := intervalFunctorHomPrism_zero _

/-- 同じ固定成分 prism の最後の辺は、元の標的図式。 -/
lemma cocartesianHomFixedComponentPrism_one {T : SSet.{u + 1}} (f : T ⟶ E) :
    (prismEndpoint 1 B ▷ T) ≫ cocartesianHomFixedComponentPrism F G c v f =
      fst B T ≫ D₁ := intervalFunctorHomPrism_one _

/-- 同じ prism の指定された底頂点への制限は、元の固定成分の区間族に定値。 -/
lemma cocartesianHomFixedComponentPrism_at {T : SSet.{u + 1}} (f : T ⟶ E) :
    (lift (𝟙 (Δ[1] : SSet.{u + 1})) (SSet.const (ULift.up (nerveVertex c))) ▷ T) ≫
        cocartesianHomFixedComponentPrism F G c v f =
      intervalMappingUncurry (SSet.const v : T ⟶ _) := by
  have h := intervalFunctorHomPrism_evaluateOfEq (f ≫ vertexFiberι p v)
    (ULift.up (nerveVertex c))
    (x := coherentNerveVertex (cocartesianTransportDiagramValue F c))
    (y := coherentNerveVertex (cocartesianTransportDiagramValue G c))
    (by simpa only [evaluateFunctorAt_functorVertex, cocartesianTransportDiagramValueFunctor] using
      qCatDiagramCoherentNerve_vertex (cocartesianTransportDiagramValueFunctor F) c)
    (by simpa only [evaluateFunctorAt_functorVertex, cocartesianTransportDiagramValueFunctor] using
      qCatDiagramCoherentNerve_vertex (cocartesianTransportDiagramValueFunctor G) c)
  change _ = intervalMappingUncurry ((f ≫ vertexFiberι p v) ≫ p) at h
  rw [Category.assoc, vertexFiberι_comp, SSet.comp_const] at h
  exact h

/-- 元の固定成分 fiber の族は、この三辺固定の prism 全体で一意に決まる。 -/
lemma cocartesianHomFixedComponentPrism_injective {T : SSet.{u + 1}} :
    Function.Injective (cocartesianHomFixedComponentPrism F G c v (T := T)) := by
  intro f g h
  apply vertexFiber_hom_ext p v
  exact intervalFunctorHomPrism_injective D₀ D₁ h

end SerrePositivity.InfinityCategories
