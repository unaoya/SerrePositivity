module

public import SerrePositivity.InfinityCategories.F1B.KanScaffoldComparison
public import SerrePositivity.InfinityCategories.Core.VertexFiberMap

/-!
概要：通常の nerve 上の left fibrations の射の fiber ごとの同値判定。
方針：元の universal scaffold に射を後合成し、二つの scaffold 比較の同値性から射を消去する。
規約：比較射は底を厳密に保つ。全空間の quasicategory 性は left fibration 性から導く。
使われ方：Kerodon Theorem 5.3.5.6、Corollary 5.6.0.6、復元比較の全空間への移行。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

local instance {E B : SSet.{u}} (p : E ⟶ B) [InnerFibration p] (b : B _⦋0⦌) :
    Quasicategory (vertexFiber p b) := vertexFiber_quasicategory_of_innerFibration p b

/-- 概要：scaffold の fiber 比較は底上の射の後合成と可換。
方針：fiber の包含へ合成し、各比較射の持ち上げの定義を使う。
規約：後合成する射の fibration 性は不要。
使われ方：Kerodon Theorem 5.3.5.6、fiber ごとの同値を scaffold の条件へ移す。 -/
lemma kanScaffoldFiberMap_postcomp
    {C : Type u} [Category.{u} C] {E E' : SSet.{u}}
    (p : E ⟶ nerve C) (q : E' ⟶ nerve C) (f : E ⟶ E') (hf : f ≫ q = p)
    (F : C ⥤ SSet.{u}) (l : simplicialReplacement F ⟶ E)
    (h : l ≫ p = simplicialReplacementProjection F)
    (h' : (l ≫ f) ≫ q = simplicialReplacementProjection F) (c : C) :
    kanScaffoldFiberMap q F (l ≫ f) h' c =
      kanScaffoldFiberMap p F l h c ≫ vertexFiberMap p q f hf (nerveVertex c) := by
  apply vertexFiber_hom_ext
  simp only [kanScaffoldFiberMap, Category.assoc, vertexFiberMap_ι, vertexFiberLift_ι]
  simp only [← Category.assoc, vertexFiberLift_ι]

/-- 概要：通常の nerve 上の left fibrations の射は各対象の fiber で同値なら前合成同値。
方針：universal scaffold の後合成が再び scaffold になることを示し、元の比較を消去する。
規約：条件は通常の圏の各対象での fiber 比較だけでよい。
使われ方：Kerodon Theorem 5.3.5.6、strict と coherent な復元候補の比較。 -/
lemma kanIsPrecompositionEquivalence_of_leftFibration_nerve_fibers
    {C : Type u} [Category.{u} C] {E E' : SSet.{u}}
    (p : E ⟶ nerve C) (q : E' ⟶ nerve C) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ E') (hf : f ≫ q = p)
    (h : ∀ c : C, IsQCatEquivalence (vertexFiberMap p q f hf (nerveVertex c))) :
    IsPrecompositionEquivalence f := by
  let F := kanCocartesianStrictTransportDiagram p
  let l := kanUniversalScaffold p
  have hl : l ≫ p = simplicialReplacementProjection F := kanUniversalScaffold_projection p
  have hl' : (l ≫ f) ≫ q = simplicialReplacementProjection F := by
    rw [Category.assoc, hf, hl]
  have (c : C) : Quasicategory (F.obj c) :=
    kanCocartesianStrictTransportDiagram_quasicategory p c
  have hs : KanCocartesianScaffold q F (l ≫ f) := by
    refine ⟨hl', ?_, ?_⟩
    · intro c d g x
      exact isCocartesianEdge_of_leftFibration q _
    · intro c
      rw [kanScaffoldFiberMap_postcomp p q f hf F l hl hl' c]
      exact ((kanUniversalScaffold_isCocartesianScaffold p).fiber c).comp (h c)
  exact (kanUniversalScaffold_isPrecompositionEquivalence p).cancel_left
    hs.isPrecompositionEquivalence

end SerrePositivity.InfinityCategories.F1B
