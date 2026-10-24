module

public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeLeftFunctorInitial
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeLeftRestrictionExistence
public import SerrePositivity.InfinityCategories.Core.FullyFaithfulBoundary

/-!
概要：元の相対左 Kan 関手の全部分圏からの制限の充満忠実性と自明 Kan 性。
方針：指定 pinched 比較の同値に全部分圏の包含を合成し、厳密な頂点全射性を合わせる。
規約：相対 join の図式でなく元の C 上の関手全体を使う。
使われ方：一般の isofibration 上での左 Kan 拡張の coherent な選択の制限定理。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：元の相対左 Kan 関手の全部分圏からの相対制限は充満忠実。
方針：元の関手の始点境界充填による指定 pinched 比較と全部分圏の比較を合成する。
規約：局所相対余極限の存在は追加仮定にしない。
使われ方：一般の標的上の元の Kan 関手の写像空間の普遍性。 -/
lemma kanRelativeLeftKanRestriction_isFullyFaithful {K C D E : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D] [Quasicategory E]
    (U : D ⟶ E) (hU : SerrePositivity.InfinityCategories.F1B.EquivalenceLifting U)
    (δ : K ⟶ C) [Mono δ] [InnerFibration δ] (hδ : IsFullyFaithful δ)
    (s : internalHom.PullbackObjObj δ U) :
    IsFullyFaithful (kanRelativeLeftKanRestriction U δ s) := by
  have : InnerFibration U := hU.innerFibration
  have : Quasicategory s.pt := kanRelativeInternalHomTarget_quasicategory U _ s
  have : Quasicategory ((internalHom.obj (Opposite.op C)).obj D) :=
    inferInstanceAs (Quasicategory ((ihom C).obj D))
  intro x y
  have hx := fullSubcomplexOnVertices_vertex x
  change KanRelativeLeftKanVertex U δ x.val at hx
  let F := (functorVertexEquiv C D).symm x.val
  have hF : functorVertex F = x.val := (functorVertexEquiv C D).apply_symm_apply _
  have hinit : InitialBoundaryLifting s.π x.val := by
    rw [← hF]
    exact kanRelativeLeftFunctor_relative_initialBoundary δ hδ U hU s F hx
  change IsSimplicialHomotopyEquivalence
    (pinchedHomMap ((kanRelativeLeftKanDiagrams U δ).ι ≫ s.π) x y)
  rw [pinchedHomMap_comp]
  exact (isFullyFaithful_fullSubcomplexOnVertices_ι _ _ x y).comp
    (SerrePositivity.InfinityCategories.F1B.pinchedHomMap_equivalence_of_initialBoundary _ x.val y.val hinit)

/-- 概要：標準局所相対余極限が存在すれば元の相対左 Kan 制限は自明 Kan。
方針：充満忠実性と inner 性に、元と底を厳密に保つ存在による頂点全射性を合わせる。
規約：δ は充満忠実な inner 単射、U は同値を持ち上げる。
使われ方：元の相対 Kan 関手の coherent な選択と制限の可縮な fiber。 -/
lemma kanRelativeLeftKanRestriction_trivialKanFibration {K C D E : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D] [Quasicategory E]
    (U : D ⟶ E) (hU : SerrePositivity.InfinityCategories.F1B.EquivalenceLifting U)
    (δ : K ⟶ C) [Mono δ] [InnerFibration δ] (hδ : IsFullyFaithful δ)
    (s : internalHom.PullbackObjObj δ U)
    (hlocal : ∀ (F₀ : K ⟶ D) (H₀ : C ⟶ E), F₀ ≫ U = δ ≫ H₀ →
      ∀ c : C _⦋0⦌, ∃ z : JoinCocone (leftKanDiagram δ F₀ c),
        IsRelativeColimitCone U z ∧ z.val ≫ U = (leftKanCanonicalCocone δ H₀ c).val) :
    TrivialKanFibration (kanRelativeLeftKanRestriction U δ s) := by
  have : InnerFibration U := hU.innerFibration
  have := kanRelativeLeftKanRestriction_innerFibration U hU δ s
  have : Quasicategory s.pt := kanRelativeInternalHomTarget_quasicategory U _ s
  have : Quasicategory (kanRelativeLeftKanDiagrams U δ : SSet.{u}) :=
    inferInstanceAs (Quasicategory
      (fullSubcomplexOnVertices _ (KanRelativeLeftKanVertex U δ) : SSet.{u}))
  have hf := kanRelativeLeftKanRestriction_isFullyFaithful U hU δ hδ s
  exact hf.trivialKanFibration_of_surjective
    (kanRelativeLeftKanRestriction_surjective U hU δ hδ s hlocal)

end SerrePositivity.InfinityCategories.F1B
