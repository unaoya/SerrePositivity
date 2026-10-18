module

public import SerrePositivity.KST.Descent.IntegralDescentStep
public import SerrePositivity.KST.Descent.ComponentCount
public import SerrePositivity.KST.Descent.SeparatedObjects
public import SerrePositivity.KST.Descent.ClosedCoverIntersectionGeometry

/-!
# 可約な被約基底の帰納段階

## 概要
低次元の帰納仮定と、既約成分数が少ない基底の帰納仮定から、閉和の局所降下を供給する。

## 方針
一つの整成分と残りを取り、交わりには次元の帰納、残りには成分数の帰納を適用する。

## 規約
二つの帰納仮定はそれぞれ厳密に小さい次元・成分数に限り、前層の公理には含めない。

## 使われ方
論文 補題 3.3・定理 3.1 の「整 → 被約」の閉和の段階。
-/

@[expose] public section

universe u w t

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace SerrePositivity.KST.Descent

/-- 概要：次元上界を固定し、成分数が少ない被約基底への帰納仮定（論文 定理 3.1）。
方針：実際の基底の既約成分数を使う。
規約：厳密な個数の減少を要求し、同じ基底の結論を仮定しない。
使われ方：残りの閉和上の局所降下。 -/
def SectionedDescentFewerComponents {S : Scheme.{u}} {Coefficient : Type w}
    (L : GradedPresheaf.{u + 1, u, w, t} (FiniteTypeSchemes S) Coefficient)
    (G : Type u) [Group G] (d n : ℕ) : Prop :=
  ∀ (B V : FiniteTypeSchemes S) [IsReduced B.obj.left] [IsSeparated V.obj.hom]
    (p : V ⟶ B) (action : G →* Aut V) (over_base : ∀ g, (action g).asIso.hom ≫ p = p)
    (s : B ⟶ V), s ≫ p = 𝟙 B →
    (∀ x y : V.obj.left, p.hom.left x = p.hom.left y →
      ∃ g : G, (action g).asIso.hom.hom.left x = y) →
    topologicalKrullDim B.obj.left ≤ d → Nat.card (IrreducibleComponentIndex B) < n →
      L.PiDescent p action over_base

namespace NaturalBlowupSequences

variable {S : Scheme.{u}} [IsNoetherian S] {Coefficient : Type w}
variable {L : GradedPresheaf.{u + 1, u, w, t} (FiniteTypeSchemes S) Coefficient}
variable (data : NaturalBlowupSequences L) [Nilinvariant S L]
variable [∀ H n, PreservesFiniteProducts (L H n)]
variable {G : Type u} [Group G] [Finite G]

include data

/-- 概要：被約な基底と始域の閉和の段階を二つの厳密な帰納で閉じる（論文 定理 3.1）。
方針：整成分・残り・交わりの三つの指定降下を構成して貼り合わせる。
規約：閉和の局所降下を別の仮定にせず、それぞれの帰納から供給する。
使われ方：既約成分数の強い帰納の一段。 -/
theorem reducedSource_piDescent_of_below_and_fewer {B V : FiniteTypeSchemes S}
    [IsReduced B.obj.left] [IsReduced V.obj.left] [IsSeparated V.obj.hom]
    (p : V ⟶ B) (action : G →* Aut V) (over_base : ∀ g, (action g).asIso.hom ≫ p = p)
    (s : B ⟶ V) (hs : s ≫ p = 𝟙 B)
    (transitive : ∀ x y : V.obj.left, p.hom.left x = p.hom.left y →
      ∃ g : G, (action g).asIso.hom.hom.left x = y)
    (d : ℕ) (bound : topologicalKrullDim B.obj.left ≤ d)
    (below : SectionedDescentBelow L G d)
    (fewer : SectionedDescentFewerComponents L G d
      (Nat.card (IrreducibleComponentIndex B))) : L.PiDescent p action over_base := by
  classical
  by_cases empty : IsEmpty B.obj.left
  · let := empty
    exact L.piDescent_of_empty_target p action over_base
  by_cases integral : IsIntegral B.obj.left
  · let := integral
    exact data.integral_piDescent_of_below p action over_base s hs transitive d bound below
  have nonempty : Nonempty B.obj.left := not_isEmpty_iff.mp empty
  let x := Classical.choice nonempty
  let c : IrreducibleComponentIndex B :=
    ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
  let Y := integralComponent B c
  let R := reducedClosedAsFiniteType B (componentRemainder B c)
  let i : Y ⟶ B := integralComponentInclusion B c
  let j : R ⟶ B := reducedClosedAsFiniteTypeInclusion B (componentRemainder B c)
  let Pi := closedImmersionPullback p i
  let Pj := closedImmersionPullback p j
  have : IsSeparated Pi.obj.hom := closedImmersionPullback_isSeparated p i
  have : IsSeparated Pj.obj.hom := closedImmersionPullback_isSeparated p j
  have : IsSeparated (closedCoverPullbackSquare p i j).X₁.obj.hom :=
    closedCoverPullbackIntersection_isSeparated p i j
  have left_descent := data.integral_piDescent_of_below (B := Y) (V := Pi)
    (closedImmersionSquare p i).f₁₃ (closedBaseChangeAction p i action over_base)
    (closedBaseChangeAction_over_base p i action over_base) (closedBaseChangeSection p i s hs)
    (closedBaseChangeSection_identity p i s hs)
    (closedBaseChangeAction_transitive_on_fibers p i action over_base transitive) d
    ((integralComponent_dimension_le B c).trans bound) below
  have remainder_bound : topologicalKrullDim R.obj.left ≤ d := by
    change topologicalKrullDim (reducedClosedSubscheme (componentRemainder B c)) ≤ d
    rw [reducedClosedSubscheme_dimension]
    exact (topologicalKrullDim_subspace_le B.obj.left _).trans bound
  have right_descent := fewer R Pj (closedImmersionSquare p j).f₁₃
    (closedBaseChangeAction p j action over_base)
    (closedBaseChangeAction_over_base p j action over_base)
    (closedBaseChangeSection p j s hs) (closedBaseChangeSection_identity p j s hs)
    (closedBaseChangeAction_transitive_on_fibers p j action over_base transitive) remainder_bound
    (componentRemainder_componentCount_lt B c)
  have intersection_descent := below (closedImmersionSquare i j).X₁
    (closedCoverPullbackSquare p i j).X₁ (closedCoverPullbackCube p i j).τ₁
    (closedCoverPullbackSquareAction p i j action over_base).on1
    (closedCoverIntersection_invariant p i j action over_base)
    (closedCoverIntersectionSection p i j s hs) (closedCoverIntersectionSection_identity p i j s hs)
    (closedCoverIntersection_transitive_on_fibers p i j action over_base transitive)
    (componentSplit_intersection_dimension_lt_bound B c d bound)
  exact data.closedCover_piDescent p i j action over_base (componentSplit_covering B c)
    left_descent right_descent intersection_descent

/-- 概要：被約な基底の閉和の段階で始域の被約性を外す（論文 定理 3.1）。
方針：始域だけを被約化し、切断と推移性を移して、公理 (3) で指定比較を戻す。
規約：二つの帰納仮定の基底次元と成分数は変更しない。
使われ方：成分数の帰納で非被約な引き戻しを扱う。 -/
theorem reducedBase_piDescent_of_below_and_fewer {B V : FiniteTypeSchemes S}
    [IsReduced B.obj.left] [IsSeparated V.obj.hom]
    (p : V ⟶ B) (action : G →* Aut V) (over_base : ∀ g, (action g).asIso.hom ≫ p = p)
    (s : B ⟶ V) (hs : s ≫ p = 𝟙 B)
    (transitive : ∀ x y : V.obj.left, p.hom.left x = p.hom.left y →
      ∃ g : G, (action g).asIso.hom.hom.left x = y)
    (d : ℕ) (bound : topologicalKrullDim B.obj.left ≤ d)
    (below : SectionedDescentBelow L G d)
    (fewer : SectionedDescentFewerComponents L G d
      (Nat.card (IrreducibleComponentIndex B))) : L.PiDescent p action over_base := by
  have : IsSeparated (finiteTypeReduction V).obj.hom := finiteTypeReduction_isSeparated V
  apply (Nilinvariant.piDescent_iff_reducedSource L p action over_base).mpr
  apply data.reducedSource_piDescent_of_below_and_fewer
    (finiteTypeReductionInclusion V ≫ p) (finiteTypeReductionAction action)
    (reducedSourceAction_over_base p action over_base) (finiteTypeReductionLift s)
    _ (reducedSourceAction_transitive_on_fibers p action transitive) d bound below fewer
  exact (finiteTypeReductionLift_comp_inclusion_assoc s p).trans hs

/-- 概要：既約成分数の強い帰納を実行し、被約基底の段階を閉じる（論文 定理 3.1）。
方針：残り自身の成分数の厳密な減少を、強い自然数帰納の仮定へ渡す。
規約：成分数に関する仮定は結論に残さず、低次元の帰納仮定だけを残す。
使われ方：外側の次元帰納に対する被約基底の段階。 -/
theorem reducedBase_piDescent_of_below {B V : FiniteTypeSchemes S}
    [IsReduced B.obj.left] [IsSeparated V.obj.hom]
    (p : V ⟶ B) (action : G →* Aut V) (over_base : ∀ g, (action g).asIso.hom ≫ p = p)
    (s : B ⟶ V) (hs : s ≫ p = 𝟙 B)
    (transitive : ∀ x y : V.obj.left, p.hom.left x = p.hom.left y →
      ∃ g : G, (action g).asIso.hom.hom.left x = y)
    (d : ℕ) (bound : topologicalKrullDim B.obj.left ≤ d)
    (below : SectionedDescentBelow L G d) : L.PiDescent p action over_base := by
  have all_counts (n : ℕ) :
      ∀ (B V : FiniteTypeSchemes S) [IsReduced B.obj.left] [IsSeparated V.obj.hom]
        (p : V ⟶ B) (action : G →* Aut V) (over_base : ∀ g, (action g).asIso.hom ≫ p = p)
        (s : B ⟶ V), s ≫ p = 𝟙 B →
        (∀ x y : V.obj.left, p.hom.left x = p.hom.left y →
          ∃ g : G, (action g).asIso.hom.hom.left x = y) →
        topologicalKrullDim B.obj.left ≤ d → Nat.card (IrreducibleComponentIndex B) ≤ n →
          L.PiDescent p action over_base := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro B V _ _ p action over_base s hs transitive bound card_bound
      apply data.reducedBase_piDescent_of_below_and_fewer
        p action over_base s hs transitive d bound below
      intro B' V' _ _ p' action' over_base' s' hs' transitive' bound' fewer
      exact ih (Nat.card (IrreducibleComponentIndex B')) (fewer.trans_le card_bound)
        B' V' p' action' over_base' s' hs' transitive' bound' le_rfl
  exact all_counts (Nat.card (IrreducibleComponentIndex B))
    B V p action over_base s hs transitive bound le_rfl

/-- 概要：一般の基底の一段を低次元の帰納仮定から閉じる（論文 定理 3.1）。
方針：始域・基底を同時に被約化し、切断・推移性・次元を保持して被約な場合へ戻す。
規約：基底の被約性を結論の仮定に残さず、Noether 性と公理 (3) を明示する。
使われ方：自然数の次元上界に関する外側の帰納の一段。 -/
theorem piDescent_of_below {B V : FiniteTypeSchemes S} [IsSeparated V.obj.hom]
    (p : V ⟶ B) (action : G →* Aut V) (over_base : ∀ g, (action g).asIso.hom ≫ p = p)
    (s : B ⟶ V) (hs : s ≫ p = 𝟙 B)
    (transitive : ∀ x y : V.obj.left, p.hom.left x = p.hom.left y →
      ∃ g : G, (action g).asIso.hom.hom.left x = y)
    (d : ℕ) (bound : topologicalKrullDim B.obj.left ≤ d)
    (below : SectionedDescentBelow L G d) : L.PiDescent p action over_base := by
  have : IsSeparated (finiteTypeReduction V).obj.hom := finiteTypeReduction_isSeparated V
  apply (Nilinvariant.piDescent_iff_reduction L p action over_base).mpr
  apply data.reducedBase_piDescent_of_below
    (finiteTypeReductionMap p) (finiteTypeReductionAction action)
    (finiteTypeReductionAction_over_base p action over_base) (finiteTypeReductionMap s)
    (finiteTypeReductionMap_section p s hs)
    (finiteTypeReductionAction_transitive_on_fibers p action transitive) d _ below
  rw [finiteTypeReduction_dimension]
  exact bound

end NaturalBlowupSequences

end SerrePositivity.KST.Descent
