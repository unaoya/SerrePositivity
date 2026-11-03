module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.TriangleConeCoefficientEquality
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.IntervalZeroPrefix

/-!
概要：同じ実三角形の三辺を、元の区間族と係数付き右錐へ厳密に戻す。
方針：四角形の面の式と同じ先頭切断上での時間零の一致を使う。
規約：実全辺を保持。使われ方：元の四面体の三つの残る面。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の第一辺は、同じ係数付き区間全体の左包含。 -/
lemma triangleRightConeParameter_first (P : SSet.{u}) :
    (stdSimplex.δ (2 : Fin 3) ▷ P) ≫ triangleRightConeParameter P =
      joinInl (Δ[1] ⊗ P) Δ[0] := by
  change (stdSimplex.δ (2 : Fin 3) ▷ P) ≫
    squarePrismTriangle (rightMappingSpacePrism (Δ[1] ⊗ P)) 0 = _
  rw [squarePrismTriangle_zero_initial, rightMappingSpacePrism_zero]

/-- 元の最後辺は、元の一時刻の係数を持つ同じ実右錐。 -/
lemma triangleRightConeParameter_last (P : SSet.{u}) :
    (stdSimplex.δ (0 : Fin 3) ▷ P) ≫ triangleRightConeParameter P =
      rightMappingSpacePrism P ≫ joinMap (prismEndpoint 1 P) (𝟙 Δ[0]) := by
  change (stdSimplex.δ (0 : Fin 3) ▷ P) ≫
    squarePrismTriangle (rightMappingSpacePrism (Δ[1] ⊗ P)) 0 = _
  rw [squarePrismTriangle_zero_final, rightMappingSpacePrism_naturality]

/-- 元の長辺は、元の零時刻の係数を持つ同じ実右錐。 -/
lemma triangleRightConeParameter_long (P : SSet.{u}) :
    (stdSimplex.δ (1 : Fin 3) ▷ P) ≫ triangleRightConeParameter P =
      rightMappingSpacePrism P ≫ joinMap (prismEndpoint 0 P) (𝟙 Δ[0]) := by
  have hd : squareDiagonal.{u} = lift (𝟙 Δ[1]) (𝟙 Δ[1]) := by
    apply SSet.yonedaEquiv.injective
    apply Prod.ext <;> decide
  change (stdSimplex.δ (1 : Fin 3) ▷ P) ≫
    squarePrismTriangle (rightMappingSpacePrism (Δ[1] ⊗ P)) 0 = _
  rw [squarePrismTriangle_diagonal, hd, ← rightMappingSpacePrism_naturality]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨s, p⟩
  change (rightMappingSpacePrism (Δ[1] ⊗ P)).app (Opposite.op ⦋n⦌) (s, (s, p)) = _
  apply rightMappingSpacePrism_eq_of_prefix
  apply interval_zero_prefix
  intro i hi
  rw [intervalJoin_cut] at hi
  have h := (Join.lt_pullCut_iff (stdSimplex.objEquiv s).toOrderHom 1 i).mp hi
  change (s i).val < 1 at h
  exact Fin.ext (Nat.le_zero.mp (Nat.le_of_lt_succ h))

end SerrePositivity.InfinityCategories.F2
