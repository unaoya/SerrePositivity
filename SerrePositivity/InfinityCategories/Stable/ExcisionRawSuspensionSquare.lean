module
public import SerrePositivity.InfinityCategories.Stable.ExcisionRawSuspensionFamily
public import SerrePositivity.InfinityCategories.Core.InternalHomFlipVertices

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
namespace SerrePositivity.InfinityCategories

def excisionRawSuspensionSquare {X : SSet.{u}} (F : nerve ExcisionGridIndex.{u} ⟶ X) :
    (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X :=
  internalHomFlipHomEquiv (Δ[1] ⊗ Δ[1] : SSet.{u}) (Δ[1] ⊗ Δ[1]) X
    (excisionRawSuspensionFamily F)

lemma excisionRawSuspensionSquare_source_vertex {X : SSet.{u}}
    (F : nerve ExcisionGridIndex.{u} ⟶ X) :
    (pullbackCone (excisionRawSuspensionSquare F)).vertex =
      functorVertex (excisionGridSquareEmbedding ≫ F) := by
  rw [pullbackCone_vertex]
  change (excisionRawSuspensionSquare F).app (Opposite.op ⦋0⦌)
    (stdSimplex.obj₀Equiv.symm 0, stdSimplex.obj₀Equiv.symm 0) = _
  rw [excisionRawSuspensionSquare, internalHomFlipHomEquiv_app_zero,
    excisionRawSuspensionFamily_source]

end SerrePositivity.InfinityCategories
