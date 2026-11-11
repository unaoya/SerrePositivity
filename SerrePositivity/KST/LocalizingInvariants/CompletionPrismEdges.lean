module

public import SerrePositivity.KST.LocalizingInvariants.CompletionZeroComponent
public import Mathlib.AlgebraicTopology.SimplicialSet.HoFunctorMonoidal

/-!
概要：成分収縮の全 prism の辺が元の cofiber 分母に属することを判定する。
方針：二辺の外積の実合成二単体を写し、cofiber 分母の合成閉性を適用する。
規約：頂点成分だけでは結論せず、水平辺と垂直辺をともに検査する。
使われ方：Sp-7 の全図式収縮を元の wide 部分複体へ持ち上げる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable {C D K : SSet.{u}} [Quasicategory C] [Quasicategory D]
  [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable D] (f : C ⟶ D) [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor f]
  (h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f)
include h

/-- 概要：水平・垂直の実分母から、同じ全 prism の全ての斜辺も元の分母になる。
方針：二辺の外積の実合成二単体を写し、cofiber 分母の合成閉性を適用する。
規約：頂点成分だけでは結論せず、水平辺と垂直辺をともに検査する。
使われ方：Sp-7 の全図式収縮を元の wide 部分複体へ持ち上げる。 -/
lemma completionPrism_edges (H : K ⊗ (Δ[1] : SSet.{u}) ⟶ D)
    (horizontal : ∀ (e : K _⦋1⦌) (t : (Δ[1] : SSet.{u}) _⦋0⦌),
      H.app _ (e, (Δ[1] : SSet.{u}).σ 0 t) ∈
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges (completionEssentialImage f))
    (vertical : ∀ (k : K _⦋0⦌) (a : (Δ[1] : SSet.{u}) _⦋1⦌),
      H.app _ (K.σ 0 k, a) ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges (completionEssentialImage f))
    (s : (K ⊗ (Δ[1] : SSet.{u})) _⦋1⦌) :
    H.app _ s ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges (completionEssentialImage f) := by
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex s.1
  let a := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex s.2
  let c := (Truncated.Edge.CompStruct.compId e).tensor
    (Truncated.Edge.CompStruct.idComp a)
  have ht := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberStableEdges_compStruct_twoOfThree (completionEssentialImage f)
    (c.map ((truncation 2).map H))
  rw [stableClosure_completionEssentialImage f h.2.1] at ht
  exact ht.1 (horizontal s.1 ((Δ[1] : SSet.{u}).δ 1 s.2))
    (vertical (K.δ 0 s.1) s.2)

end SerrePositivity.KST.LocalizingInvariants
