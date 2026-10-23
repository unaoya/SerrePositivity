module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SiftedTerminalComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.SpaceTerminal
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FiberwisePullbackKanObjects
public import SerrePositivity.InfinityCategories.F1.CoherentKanInvertible

/-!
概要：sifted 添字の全空間 Kan 模型を、空間の ∞ 圏の native な空積にする。
方針：元の一点への比較射の弱同値性を同じ coherent 辺の可逆性へ移す。
規約：頂点は元の Kan 置換、比較射は元の一点への射。
使われ方：sifted 余極限と有限積の交換の空積の場合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の全空間 Kan 模型から、元の一点 Kan 対象への指定された比較。 -/
def siftedTerminalKanMap (K : SSet.{u}) : F2.continuousKanObject K ⟶ pointKanObject.{u} :=
  stdSimplex.isTerminalObj₀.from _

/-- 一点への比較と元の Kan 置換単位は厳密に可換。 -/
lemma siftedTerminalKanMap_unit (K : SSet.{u}) :
    F2.continuousKanReplacementUnit.app K ≫ siftedTerminalKanMap K =
      stdSimplex.isTerminalObj₀.from K :=
  stdSimplex.isTerminalObj₀.hom_ext _ _

/-- sifted 添字の元の一点比較は、実際の Kan 対象間の同値。 -/
lemma siftedTerminalKanMap_isQCatEquivalence (K : SSet.{u}) [IsSiftedInfinity K] :
    IsQCatEquivalence (siftedTerminalKanMap K) := by
  have hpt : IsContractibleKan pointKanObject.{u}.obj := by
    intro n b
    exact ⟨stdSimplex.isTerminalObj₀.from Δ[n], stdSimplex.isTerminalObj₀.hom_ext _ _⟩
  have h : IsWeakHomotopyEquivalence ((siftedTerminalKanMap K : F2.continuousKanReplacement.obj K ⟶
      pointKanObject.{u}.obj) ≫ terminal.from pointKanObject.{u}.obj) := by
    convert continuousKanTerminalComparison_isWeakHomotopyEquivalence_of_sifted K using 1 <;>
      first | rfl | exact terminal.hom_ext (C := SSet.{u}) _ _
  have he := (hpt.isWeaklyContractible.cancel_right h).isSimplicialHomotopyEquivalence
  exact he.isQCatEquivalence

/-- sifted 添字の元の全空間 Kan 模型は、空間の ∞ 圏の終対象。 -/
lemma siftedTotalVertex_isTerminal (K : SSet.{u}) [IsSiftedInfinity K] :
    IsTerminalVertex (coherentNerveVertex (F2.continuousKanObject K)) := by
  have h := coherentKanEdge_isInvertible_of_isQCatEquivalence
    (siftedTerminalKanMap_isQCatEquivalence K)
  have : IsIso (Truncated.HomotopyCategory.homMk
    (coherentNerveEdge (siftedTerminalKanMap K)).toTruncated) := h
  let e := asIso (Truncated.HomotopyCategory.homMk (coherentNerveEdge
    (siftedTerminalKanMap K)).toTruncated)
  have ht : IsTerminalVertex (coherentNerveVertex pointKanObject.{u}) := by
    simpa only [pointSpaceVertex, spaceInfinityVertex_eq_coherent] using
      pointSpaceVertex_isTerminalVertex.{u}
  exact ht.of_vertexIso e.symm

/-- 元の全空間 Kan 模型を頂点とする、空図式の native な錐。 -/
def siftedEmptyProductNativeCone (K : SSet.{u}) :
    JoinCone (⊥ : SpaceInfinity.{u}.Subcomplex).ι :=
  emptyCone (coherentNerveVertex (F2.continuousKanObject K))

/-- sifted な底の元の全空間 Kan 模型の空錐は native な極限錐。 -/
lemma siftedEmptyProductNativeCone_isLimit (K : SSet.{u}) [IsSiftedInfinity K] :
    IsLimitCone (siftedEmptyProductNativeCone K) :=
  (isLimitCone_emptyCone_iff _).mpr (siftedTotalVertex_isTerminal K)

end SerrePositivity.InfinityCategories.HomotopyLimits
