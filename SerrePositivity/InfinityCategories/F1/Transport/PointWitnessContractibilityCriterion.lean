module

public import SerrePositivity.InfinityCategories.F1.Transport.PointWitnessIntervalBoundary
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.RightIntervalEquivalence
public import SerrePositivity.InfinityCategories.Core.TerminalMappingSpace

/-!
概要：区間族の境界制限の trivial Kan 性と非空性から点上の表現空間の可縮性を得る。
方針：全ての両端固定区間写像空間を可縮にし、右写像空間による終対象判定を使う。
規約：非空性の構成は小ささを用いる次の段階で供給する。
使われ方：Kerodon Lemma 5.6.9.2 の可縮性の部分。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：非空な quasicategory の区間族の境界制限が trivial Kan なら全体は可縮 Kan。
方針：各右写像空間へ可縮性を移し全頂点の終対象性を判定する。
規約：区間の境界制限は実際の内部 Hom の射。
使われ方：点上の表現空間の可縮性の最終判定。 -/
lemma isContractibleKan_of_nonempty_of_intervalBoundary {X : SSet.{u}} [Quasicategory X]
    (hX : Nonempty (X _⦋0⦌))
    (h : TrivialKanFibration ((pre (boundary 1).ι).app X)) : IsContractibleKan X := by
  have := h
  apply isContractibleKan_of_nonempty_of_all_terminal hX
  intro x
  apply isTerminalVertex_of_pinchedHom_isContractibleKan x
  intro z
  have hc : IsContractibleKan (intervalMappingSpace z x) :=
    vertexFiber_isContractibleKan ((pre (boundary 1).ι).app X)
      (functorVertex (intervalMappingBoundary z x))
  exact (pinchedHomToIntervalMappingSpace_isQCatEquivalence z x).choose.isContractibleKan_iff.mpr hc

/-- 概要：点上の実際の表現空間は非空なら可縮 Kan 複体。
方針：実際の区間境界制限定理を移した境界制限と一般の可縮性判定を使う。
規約：非空性は明示的な補助入力であり、主定理では小ささから構成する。
使われ方：点上の表現空間の非空性を可縮性へ渡す。 -/
lemma pointWitnessSpace_isContractibleKan_of_nonempty (E : SSet.{u + 1}) [KanComplex E]
    (hE : Nonempty ((transportWitnessSpace (transportPointProjection E)) _⦋0⦌)) :
    IsContractibleKan (transportWitnessSpace (transportPointProjection E)) :=
  isContractibleKan_of_nonempty_of_intervalBoundary hE
    (pointWitnessIntervalBoundary_trivialKanFibration E)

end SerrePositivity.InfinityCategories
