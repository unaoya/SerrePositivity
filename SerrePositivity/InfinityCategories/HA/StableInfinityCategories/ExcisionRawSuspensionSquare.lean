module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionRawSuspensionFamily
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InternalHomFlipVertices

/-!
概要：全パラメーターに整合する実錐比較を、矢印圏の四角形へ移す。
方針：元の全単体・同じ比較辺・指定頂点への錐の移送を保持する。
規約：一般安定性を仮定しない。使われ方：HA 1.4.2.15 の第二条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open MorphismProperty
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

def excisionRawSuspensionSquare {X : SSet.{u}} (F : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u} ⟶ X) :
    (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (Δ[1] ⊗ Δ[1] : SSet.{u}) (Δ[1] ⊗ Δ[1]) X
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionRawSuspensionFamily F)

lemma excisionRawSuspensionSquare_source_vertex {X : SSet.{u}}
    (F : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u} ⟶ X) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone (excisionRawSuspensionSquare F)).vertex =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSquareEmbedding ≫ F) := by
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pullbackCone_vertex]
  change (excisionRawSuspensionSquare F).app (Opposite.op ⦋0⦌)
    (stdSimplex.obj₀Equiv.symm 0, stdSimplex.obj₀Equiv.symm 0) = _
  rw [excisionRawSuspensionSquare, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.internalHomFlipHomEquiv_app_zero,
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionRawSuspensionFamily_source]

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
