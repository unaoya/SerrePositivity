module

public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafPointwiseLimits
public import SerrePositivity.InfinityCategories.F1.Coherent.SpaceSmallLimits

/-!
概要：前層の小さい極限を各点で構成し、元の全評価による保存・検出を無条件で示す。
方針：任意の小さい空間値図式の極限を、既存の各点構成へ入力する。
規約：小さい底と小さい形状を使い、各点の存在の追加仮定を要求しない。
使われ方：F1-4、HTT 5.1.2.2–5.1.2.4、Ind の基盤。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable {B C : SSet.{u}}
  (p : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ PresheafInfinity C)

/-- 各点の小さい空間値極限から、同じ前層図式の自然な極限全錐を構成できる。 -/
lemma presheafInfinity_exists_limitCone :
    ∃ c : JoinCone p, IsLimitCone c ∧ ∀ x : C _⦋0⦌,
      IsLimitCone (mapJoinCone (presheafInfinityEvaluation x) c) :=
  presheafInfinity_exists_limitCone_of_evaluation p
    (fun x ↦ hasLimit_coherentSpaceDiagram (p ≫ presheafInfinityEvaluation x))

/-- 任意の小さい形状の元の前層図式は極限を持つ。 -/
lemma presheafInfinity_hasLimit : HasLimit p :=
  presheafInfinity_hasLimit_of_evaluation p
    (fun x ↦ hasLimit_coherentSpaceDiagram (p ≫ presheafInfinityEvaluation x))

/-- 同じ小さい前層図式の任意の極限全錐は元の各評価で極限となる。 -/
lemma presheafInfinity_evaluation_small_isLimit (c : JoinCone p) (hc : IsLimitCone c)
    (x : C _⦋0⦌) : IsLimitCone (mapJoinCone (presheafInfinityEvaluation x) c) :=
  presheafInfinity_evaluation_isLimit p
    (fun x ↦ hasLimit_coherentSpaceDiagram (p ≫ presheafInfinityEvaluation x)) c hc x

/-- 小さい形状の前層錐の極限性は、元の全評価により保存・検出される。 -/
lemma presheafInfinity_small_isLimit_iff_evaluation (c : JoinCone p) :
    IsLimitCone c ↔ ∀ x : C _⦋0⦌,
      IsLimitCone (mapJoinCone (presheafInfinityEvaluation x) c) :=
  ⟨presheafInfinity_evaluation_small_isLimit p c, presheafInfinity_isLimit_of_evaluation p c⟩

end SerrePositivity.InfinityCategories
