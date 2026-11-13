module

public import SerrePositivity.KST.Spectra.SpectrumZeroObject
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorTerminal
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorInitial
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroDiagramComparison

/-!
概要：任意のパラメータ単体集合上の Sp 値関手の実際の零対象。
方針：一点スペクトルの定値図式を使い、始・終対象の点ごとの判定を両方適用する。
規約：Sp の安定性を仮定しない。使われ方：普遍評価の零角の coherent な因子分解。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum

/-- 元の一点スペクトルによる定値零図式。 -/
def constantZeroDiagram (K : SSet.{u + 1}) : K ⟶ Sp.{u} := SSet.const pointZeroVertex.vertex

/-- 元の定値零図式は各頂点で実際の零対象を値に取る。 -/
lemma constantZeroDiagram_vertex_isZero (K : SSet.{u + 1}) (k : K _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((constantZeroDiagram K).app _ k) := by
  rw [constantZeroDiagram, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroDiagram_const_vertex]
  exact pointZeroVertex.isZero

/-- 全ての高次単体を持つ関手単体集合の実際の零頂点。 -/
def functorZeroVertex (K : SSet.{u + 1}) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroVertex ((ihom K).obj Sp.{u}) where
  vertex := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (constantZeroDiagram K)
  isInitial := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isInitialVertex_functorVertex_of_pointwise _
    (fun k ↦ (constantZeroDiagram_vertex_isZero K k).1)
  isTerminal := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isTerminalVertex_functorVertex_of_pointwise _
    (fun k ↦ (constantZeroDiagram_vertex_isZero K k).2)

/-- Sp 値関手の関手単体集合は、安定性を仮定せず零対象を持つ。 -/
instance spFunctor_hasZeroVertex (K : SSet.{u + 1}) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex ((ihom K).obj Sp.{u}) :=
  ⟨⟨(functorZeroVertex K).vertex, (functorZeroVertex K).isZero⟩⟩

end SerrePositivity.KST.Spectra.OmegaSpectrum
