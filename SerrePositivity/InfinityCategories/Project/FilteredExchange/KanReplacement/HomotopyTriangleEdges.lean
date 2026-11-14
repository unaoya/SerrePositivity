module

public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismContraction

/-!
概要：指定ホモトピーを三角形で合成するための端点と退化面の厳密な式。
方針：零単体・一次単体の Yoneda 表示で有限個の頂点を計算する。
規約：二辺は 0→1 と 1→2、合成辺は 0→2。
使われ方：指定部分円柱を保つ相対ホモトピーの合成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：標準区間の零端点との積は元の prism の零端点へ因子分解。
方針：零端点は定値射。規約：全パラメータ。使われ方：二円柱の接続点の照合。 -/
lemma intervalVertex_zero_tensor (K : SSet.{u}) :
    (stdSimplex.δ (1 : Fin 2) ▷ K) = snd (Δ[0] : SSet.{u}) K ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K := by
  rw [stdSimplex.δ_one_eq_const]
  rfl

/-- 概要：標準区間の一端点との積は元の prism の一端点へ因子分解。
方針：一端点は定値射。規約：全パラメータ。使われ方：二円柱の接続点の照合。 -/
lemma intervalVertex_one_tensor (K : SSet.{u}) :
    (stdSimplex.δ (0 : Fin 2) ▷ K) = snd (Δ[0] : SSet.{u}) K ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K := by
  rw [stdSimplex.δ_zero_eq_const]
  rfl

/-- 概要：合成辺の始点は第一辺の始点。
方針：零単体で計算。規約：三角形の頂点零。使われ方：合成円柱の始点。 -/
lemma homotopyTriangle_long_zero :
    stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (1 : Fin 3) =
      stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3) := by
  apply SSet.yonedaEquiv.injective
  decide

/-- 概要：合成辺の終点は第二辺の終点。
方針：零単体で計算。規約：三角形の頂点二。使われ方：合成円柱の終点。 -/
lemma homotopyTriangle_long_one :
    stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (1 : Fin 3) =
      stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3) := by
  apply SSet.yonedaEquiv.injective
  decide

/-- 概要：最初の二頂点を潰す退化三角形の第一辺は零で定値。
方針：一次単体で計算。規約：σ₀。使われ方：始端で定値な境界円柱の合成。 -/
lemma homotopyTriangle_degenerate_zero_first :
    stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.σ (0 : Fin 2) =
      stdSimplex.σ (0 : Fin 1) ≫ stdSimplex.δ (1 : Fin 2) := by
  apply SSet.yonedaEquiv.injective
  decide

/-- 概要：σ₀ の第二辺は元の区間。
方針：一次単体で計算。規約：厳密な式。使われ方：指定された第二境界円柱。 -/
lemma homotopyTriangle_degenerate_zero_last :
    stdSimplex.δ (0 : Fin 3) ≫ stdSimplex.σ (0 : Fin 2) = 𝟙 (Δ[1] : SSet.{u}) := by
  apply SSet.yonedaEquiv.injective
  decide

/-- 概要：σ₀ の合成辺も元の区間。
方針：一次単体で計算。規約：厳密な式。使われ方：指定境界円柱の保持。 -/
lemma homotopyTriangle_degenerate_zero_long :
    stdSimplex.δ (1 : Fin 3) ≫ stdSimplex.σ (0 : Fin 2) = 𝟙 (Δ[1] : SSet.{u}) := by
  apply SSet.yonedaEquiv.injective
  decide

/-- 概要：合成辺と第一辺の始点は任意のパラメータでも一致する。
方針：定値な零端点を計算。規約：厳密な式。使われ方：合成円柱の始点。 -/
lemma homotopyTriangle_long_zero_prism (K : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ (stdSimplex.δ (1 : Fin 3) ▷ K) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ (stdSimplex.δ (2 : Fin 3) ▷ K) := by rfl

/-- 概要：合成辺と第二辺の終点は任意のパラメータでも一致する。
方針：定値な一端点を計算。規約：厳密な式。使われ方：合成円柱の終点。 -/
lemma homotopyTriangle_long_one_prism (K : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K ≫ (stdSimplex.δ (1 : Fin 3) ▷ K) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K ≫ (stdSimplex.δ (0 : Fin 3) ▷ K) := by rfl

end SerrePositivity.InfinityCategories.Project.FilteredExchange
