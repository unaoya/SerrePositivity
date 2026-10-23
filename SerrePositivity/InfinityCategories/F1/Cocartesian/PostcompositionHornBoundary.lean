module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.PostcompositionDiagonalVertex
public import SerrePositivity.InfinityCategories.F1.Cocartesian.IntervalSourceComposition
public import SerrePositivity.InfinityCategories.F1.Cocartesian.IntervalOuterHorn
public import SerrePositivity.InfinityCategories.F1.CospanHomHorn

/-!
概要：元の後合成の指定対角から作る外ホーンを、元の比較の指定外ホーンと同定する。
方針：全パラメーターで対角と標的辺を照合し、外ホーンの pushout を使う。
規約：元の固定成分と元の指定合成三角形を保持する。
使われ方：対角 fiber の厳密な同型を元の固定成分比較へ接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable (F G : CocartesianTransportDiagramCategory (ULift.{u} (Fin 2)))
variable (b : ((SSet.uliftFunctor.{u + 1, u}).obj
  (SimplicialCategory.sHom (cocartesianTransportDiagramValue F (ULift.up 1))
    (cocartesianTransportDiagramValue G (ULift.up 1)))) _⦋0⦌)
local notation "x" => coherentNerveVertex (cocartesianTransportDiagramValue F (ULift.up 0))
local notation "g" => cocartesianIntervalCompositionFirstEdge G
local notation "v" => NatTrans.app
  (coherentHomIntervalComparison (cocartesianTransportDiagramValue F (ULift.up 1))
    (cocartesianTransportDiagramValue G (ULift.up 1))) (Opposite.op ⦋0⦌) b
local notation "d" => cocartesianPostcompositionDiagonalVertex F G b
local notation "s₀" => cocartesianIntervalSourceCompositionVertex F G b

/-- 同じ指定対角と標的辺からの外ホーン族は、元の指定合成三角形からの族と一致する。 -/
lemma cocartesianPostcompositionHornBoundary_family {T : SSet.{u + 1}} :
    (SSet.const d : T ⟶ _) ≫ cospanHomHornMap (X := CatInfinity.{u}) x g =
      (SSet.const s₀ : T ⟶ _) ≫ cocartesianIntervalOuterHornMap F G v := by
  apply uncurry_injective
  apply (horn₂₂.isPushout.map (tensorRight T)).hom_ext
  · change (horn₂₂.ι₀₂ ▷ T) ≫ _ = (horn₂₂.ι₀₂ ▷ T) ≫ _
    rw [cospanHomHornMap_diagonal, intervalMappingUncurry_const_vertex,
      cocartesianPostcompositionDiagonalVertex_edge,
      cocartesianIntervalOuterHornMap_diagonal,
      cocartesianIntervalSourceCompositionVertex_diagonal]
    rfl
  · change (horn₂₂.ι₁₂ ▷ T) ≫ _ = (horn₂₂.ι₁₂ ▷ T) ≫ _
    rw [cospanHomHornMap_target, cocartesianIntervalOuterHornMap_target]

/-- 同じ指定頂点での外ホーンは、元の比較の実際の指定外ホーンそのもの。 -/
lemma cocartesianPostcompositionHornBoundary_vertex :
    (cospanHomHornMap (X := CatInfinity.{u}) x g).app (Opposite.op ⦋0⦌) d =
      (cocartesianIntervalOuterHornMap F G v).app (Opposite.op ⦋0⦌) s₀ := by
  have h := cocartesianPostcompositionHornBoundary_family F G b (T := Δ[0])
  rw [SSet.const_comp, SSet.const_comp] at h
  have h₀ := congrArg
    (fun f => f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0)) h
  simpa [SSet.const] using h₀

end SerrePositivity.InfinityCategories
