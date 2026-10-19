module

public import SerrePositivity.InfinityCategories.F1B.KanLeftCommaCandidateImageClass
public import SerrePositivity.InfinityCategories.F1B.KanGlobalLiftingDiagram

/-!
概要：comma fiber の局所相対余極限から元と標的を厳密に保つ左 Kan 関手を作る。
方針：相対 join 上で組み立てた候補の単位の像の恒等性を使って厳密化する。
規約：出力は元の C 上の関手であり、元と底の図式を等式で保つ。
使われ方：相対左 Kan 制限の局所存在からの頂点の持ち上げ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：底の普遍図式に両立する comma 局所余極限から厳密な相対左 Kan 延長が存在する。
方針：局所余錐を相対 join で組み立て、像で恒等な候補の単位を元と底を保って厳密化する。
規約：底 H₀ と元 F₀ の両方を等式で保ち、元の関手の標準相対 Kan 条件を得る。
使われ方：一般の isofibration 上の元の相対制限の頂点全射性。 -/
lemma exists_kanRelativeLeftCanonical_strict_extension_of_comma_colimits
    {K C D E : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D] [Quasicategory E]
    (U : D ⟶ E) (hU : KanEquivalenceLifting U)
    (δ : K ⟶ C) [Mono δ] [InnerFibration δ] (hδ : IsFullyFaithful δ)
    (F₀ : K ⟶ D) (H₀ : C ⟶ E) (hFU : F₀ ≫ U = δ ≫ H₀)
    (hlocal : ∀ c : C _⦋0⦌,
      ∃ z : JoinCocone (vertexFiberι (kanLeftCommaProjection δ) c ≫ kanLeftCommaSource δ ≫ F₀),
        IsRelativeColimitCone U z ∧ z.val ≫ U = (kanRelativeJoinFiberCocone
          (kanLeftCommaProjection δ) c (kanLeftCommaUniversalDiagram δ ≫ H₀)).val) :
    ∃ G : C ⟶ D, δ ≫ G = F₀ ∧ G ≫ U = H₀ ∧
      IsRelativeLeftKanExtendedFrom U δ G := by
  have : InnerFibration U := hU.innerFibration
  have hbase : (kanLeftCommaSource δ ≫ F₀) ≫ U =
      relativeJoinInl (kanLeftCommaProjection δ) (𝟙 C) ≫
        (kanLeftCommaUniversalDiagram δ ≫ H₀) := by
    rw [Category.assoc, hFU, ← Category.assoc, ← Category.assoc,
      kanLeftCommaUniversalDiagram_inl]
  obtain ⟨H, hH, hHU, hc⟩ :=
    exists_kanGlobalRelative_diagram_with_relative_colimits_of_lifting
      (kanLeftCommaProjection δ) U hU (kanLeftCommaSource δ ≫ F₀)
      (kanLeftCommaUniversalDiagram δ ≫ H₀) hbase hlocal
  let F := kanLeftCommaCandidate δ H
  let β := kanLeftCommaCandidateTransformation δ F₀ H hH
  have hβ := kanLeftCommaCandidate_isRelativeLeftKanExtension U δ F₀ H hH hc
  have hF : F ≫ U = H₀ := kanLeftCommaCandidate_postcomp δ U H H₀ hHU
  have hunit : F₀ ≫ U = (δ ≫ F) ≫ U := by rw [Category.assoc, hF]; exact hFU
  obtain ⟨G, hGδ, hGU, hG⟩ := exists_kanRelativeLeftCanonical_strictification_of_image_class
    U hU δ hδ β hβ hunit
    (kanLeftCommaCandidateTransformation_image_class δ U F₀ H hH H₀ hFU hHU hunit)
  exact ⟨G, hGδ, hGU.trans hF, hG⟩

end SerrePositivity.InfinityCategories.F1B
