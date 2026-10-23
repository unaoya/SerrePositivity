module

public import SerrePositivity.InfinityCategories.F1.Categories.QuasicategoryDiagramRealization
public import SerrePositivity.InfinityCategories.F1.Categories.QuasicategoryDiagramEvaluation

/-!
概要：Cat∞ 値の実現を底の対象で評価すると、元の core の豊穣評価を得る。
方針：定値な底図式で対角評価を計算し、curry の頂点評価へ移す。
規約：図式の全 coherent パラメーターについて厳密に可換とする。
使われ方：実際の区間 Hom 作用の各対象での同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：底の定値図式における対角評価は対象 c での豊穣評価になる。
方針：path の順序を取り出し、底の恒等射で混合 Hom を簡約する。
規約：添字順序 J は任意。
使われ方：Kerodon Corollary 5.6.0.6、全次数での評価の同定。 -/
lemma diagonalQuasicategoryDiagramEvaluation_constant_base
    {C J : Type u} [Category.{u} C] [LinearOrder J] (c : C)
    (F : EnrichedFunctor SSet.{u} (SimplicialThickening J)
      (QuasicategoryDiagramCategory C)) :
    diagonalQuasicategoryDiagramEvaluation ((Functor.const J).obj c) F =
      F.comp SSet (quasicategoryDiagramCoreEvaluationEnriched c) := by
  refine EnrichedFunctor.ext SSet (fun _ ↦ rfl) ?_
  intro i j
  simp only [eqToHom_refl, Category.comp_id]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro P
  change (diagonalQuasicategoryDiagramHom ((Functor.const J).obj c) F i j).app n P = _
  erw [diagonalQuasicategoryDiagramHom_of_le _ F i j
    (SimplicialThickening.Path.le (P.obj 0))]
  change ((F.map i j ≫ quasicategoryDiagramMixedHom (𝟙 c)
    (F.obj i) (F.obj j)).app n) P = _
  rw [quasicategoryDiagramMixedHom_base_id]
  rfl

/-- 概要：実現写像を底の対象で評価すると像の coherent な評価写像を回収する。
方針：curry の頂点評価を共同評価へ戻し、底の定値図式の式を使う。
規約：単体集合の射の厳密な等式。
使われ方：Kerodon Corollary 5.6.0.6、実現の写像空間への作用を各対象で調べる。 -/
lemma quasicategoryDiagramRealization_evaluate
    {C : Type u} [Category.{u} C] (c : C) :
    quasicategoryDiagramRealization C ≫ evaluateFunctorAt (ULift.up (nerveVertex c)) =
      quasicategoryDiagramInfinityEvaluation c := by
  rw [quasicategoryDiagramRealization, curry_evaluateFunctorAt_vertex]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro F
  change diagonalQuasicategoryDiagramEvaluation
    (strictDiagramSimplexBase (PinchedHom.constant (nerveVertex c) n)) F = _
  have hbase : strictDiagramSimplexBase (PinchedHom.constant (nerveVertex c) n) =
      (Functor.const (ULift.{u} (Fin (n + 1)))).obj c := rfl
  rw [hbase, diagonalQuasicategoryDiagramEvaluation_constant_base]
  rfl

end SerrePositivity.InfinityCategories
