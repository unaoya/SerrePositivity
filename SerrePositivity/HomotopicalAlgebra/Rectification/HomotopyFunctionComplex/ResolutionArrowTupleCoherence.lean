module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionArrowTuples
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NerveRelativeNaturalBoundary
public import SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftLifting

/-!
# 中断した任意モデル源への一般化：ResolutionArrowTupleCoherence

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：One all-center coherent family retaining the original tuple interpolations。

## 方針（定義・証明）
全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0286][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0286
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# One all-center coherent family retaining the original tuple interpolations

The old tuple maps and their actual strict-vertex boundary are retained,
including every higher tuple simplex. A natural vertex boundary supplies
the whole fixed boundary system without another coherence assumption.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.SimplicialModel
open SerrePositivity.HomotopyFunctionComplex.ResolutionArrowDiagram
open SerrePositivity.HomotopyFunctionComplex.ResolutionArrowTuples

namespace SerrePositivity.HomotopyFunctionComplex.ResolutionArrowTupleCoherence
variable (C : Type u) [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)

abbrev bigTuples := tuples C ⋙ SSet.uliftFunctor.{u, v}
abbrev bigVertices := vertices C ⋙ SSet.uliftFunctor.{u, v}
abbrev bigInclusion : bigVertices C ⟶ bigTuples C :=
  Functor.whiskerRight (inclusion C) SSet.uliftFunctor.{u, v}
abbrev bigBoundary : bigVertices C ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted.{u} (fibers C) :=
  Functor.whiskerRight (vertexData C) SSet.uliftFunctor.{u, v}

abbrev oldFamily (q : Index C) : (bigTuples C).obj q ⟶
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{u} ((fibers C).obj q) :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{u} (CoherentLiftTuples.interpolation hcof (source C q).inner
    (target C q) (arrow C q))

lemma oldFamily_boundary (q : Index C) : (bigInclusion C).app q ≫ oldFamily C hcof q =
    (bigBoundary C).app q := by
  change _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{u} (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.inclusion (StrictLift C q)) ≫
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{u} (CoherentLiftTuples.interpolation hcof (source C q).inner
      (target C q) (arrow C q)) = _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{u} _
  rw [← _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map_comp]
  exact congrArg (fun e => _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{u} e)
    (CoherentLiftTuples.interpolation_vertices hcof (source C q).inner (target C q) (arrow C q))

omit [ModelCategory SSet.{v}] in
lemma bigInclusion_mono (q : Index C) : Mono ((bigInclusion C).app q) :=
  UniverseLift.mono_map _

/-- All old interpolation maps are fixed at once, with all strict vertices fixed in all degrees. -/
def system : NerveMovingParameter.System.{u, v} (bigTuples C) (fibers C) :=
  NerveRelativeNaturalBoundary.extend (bigVertices C) (bigTuples C) (fibers C)
    (bigInclusion C) (bigBoundary C) (oldFamily C hcof) (oldFamily_boundary C hcof)
    (fillers C hcof) (bigInclusion_mono C)

lemma system_evaluate (q : Index C) : NerveMovingParameter.evaluate.{u, v}
    (bigTuples C) (fibers C) (system C hcof) q = oldFamily C hcof q :=
  NerveRelativeNaturalBoundary.extend_evaluate _ _ _ _ _ _ _ _ _ q

/-- Recover the actual original small tuple interpolation, as a full map. -/
lemma interpolation_recover (q : Index C) : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.lower
    (NerveMovingParameter.evaluate.{u, v} (bigTuples C) (fibers C) (system C hcof) q) =
    CoherentLiftTuples.interpolation hcof (source C q).inner (target C q) (arrow C q) := by
  rw [system_evaluate]
  exact _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.lower_map _

lemma vertices_fixed : system C hcof ≫ NerveMovingParameterRelative.restriction
    (bigVertices C) (bigTuples C) (bigInclusion C) (fibers C) =
    NerveNaturalBoundary.ofNatTrans (bigVertices C)
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (fibers C)) (bigBoundary C) :=
  NerveRelativeNaturalBoundary.extend_boundary _ _ _ _ _ _ _ _ _

lemma vertex_component (s : NerveSimplexEndpoint.Index (Index C)) : (system C hcof).app s ≫
    (CategoryTheory.MonoidalClosed.pre
      ((bigInclusion C).app (NerveSimplexStart.start s))).app
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{u} ((fibers C).obj (NerveSimplexEndpoint.endpoint s))) =
    SSet.stdSimplex.isTerminalObj₀.from _ ≫ RelativeChoiceSpace.name
      ((bigBoundary C).app (NerveSimplexStart.start s) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (fibers C)).map (NerveNaturalBoundary.whole s)) := by
  have h := congr_app (vertices_fixed C hcof) s
  exact h

lemma simplex_recover (q : Index C) {n : ℕ} (a : Fin (n + 1) → StrictLift C q) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.simplex a ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.lower
      (NerveMovingParameter.evaluate.{u, v} (bigTuples C) (fibers C) (system C hcof) q) =
    CoherentLiftTuples.simplex hcof (source C q).inner (target C q) (arrow C q) a := by
  rw [interpolation_recover]

end SerrePositivity.HomotopyFunctionComplex.ResolutionArrowTupleCoherence
