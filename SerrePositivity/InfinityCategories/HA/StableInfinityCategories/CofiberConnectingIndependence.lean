module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberComparisonUniqueness
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberConnecting

/-! # 指定 suspension への接続射の選択独立性

概要：始点を固定した比較ホモトピーの第三成分は、その選択によらない。
方針：四角形の比較の h の類の一意性を最後の頂点で評価する。
規約：suspension 四角形を指定して固定する。
使われ方：S4 の cofiber 三角形の接続射。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：始点を固定した二つの比較から得る短複体の第三成分は一致する。
方針：四角形の比較の類の一意性を右上の頂点で評価する。
規約：元の列は cofiber、指定 suspension を固定。
使われ方：接続射の比較ホモトピーの選択独立性。 -/
lemma cofiberComparison_τ₃_eq_of_source_fixed {X : SSet.{u}} [Quasicategory X]
    [HasZeroMorphisms (hoFunctor.obj X)] (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t)
    (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 0 0)) (H J : SSet.Homotopy t.square s.square)
    (hH : ((stdSimplex.δ (1 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge) ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      CartesianMonoidalCategory.snd Δ[0] Δ[1] ≫ SSet.const (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 0 0))
    (hJ : ((stdSimplex.δ (1 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge) ▷ (Δ[1] : SSet.{u})) ≫ J.h =
      CartesianMonoidalCategory.snd Δ[0] Δ[1] ≫ SSet.const (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 0 0)) :
    (t.hoShortComplexMapOfHomotopy s.toZeroTriangle H.h H.h₀ H.h₁).τ₃ =
      (t.hoShortComplexMapOfHomotopy s.toZeroTriangle J.h J.h₀ J.h₁).τ₃ := by
  have hh := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberSuspensionComparison_homMk_eq t.square ht s H J hH hJ
  let a := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) 1 1
  have he := congrArg (fun f ↦ (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) a)).toFunctor.map f) hh
  apply Arrow.mk_injective
  exact (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.homotopyEvaluationOfEndpoints_arrow H a).symm.trans
    ((congrArg Arrow.mk he).trans (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.homotopyEvaluationOfEndpoints_arrow J a))

/-- 概要：任意の始点固定の比較の第三成分は定義した接続射と一致する。
方針：選んだ比較の始点固定条件を用いて二つの比較の第三成分を照合する。
規約：指定 suspension への接続射。使われ方：接続射の選択独立性の利用。 -/
lemma cofiberComparison_τ₃_eq_connectingToSuspension {X : SSet.{u}} [Quasicategory X]
    [HasZeroMorphisms (hoFunctor.obj X)] (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t)
    (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 0 0)) (H : SSet.Homotopy t.square s.square)
    (hH : ((stdSimplex.δ (1 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge) ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      CartesianMonoidalCategory.snd Δ[0] Δ[1] ≫ SSet.const (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 0 0)) :
    (t.hoShortComplexMapOfHomotopy s.toZeroTriangle H.h H.h₀ H.h₁).τ₃ =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnectingToSuspension t ht s :=
  cofiberComparison_τ₃_eq_of_source_fixed t ht s H
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenCofiberSuspensionComparison t.square ht s) hH
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenCofiberSuspensionComparison_source t.square ht s)

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
