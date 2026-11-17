# K-6 c4：固定三面を保持する因子分解三単体族（採用（06:29））

- ユーザー採用（06:29）。(9) と (9b) を一括で Ind-S に発注済み。届くまでは命題を明示定理引数に取る。Ind/F1 正本へ証明を依頼する仕様であり、その存在は主張しない。
- 現行 Ind-S (9) の型は二胞体の再構成と、同じ三面を固定した充填 fiber の可縮性・比較を含む。しかし、その再構成二胞体を欠面に持つ同じ三面の充填の実構成は明記されていない。可縮性から任意の指定欠面の可填性は推論しない。
- 提案：元の二胞体 T と二つの厳密合成面を保持する因子分解三単体族 F を、F1 の汎用構成として直接供給する。欠面の長 Hom は元の T の長 Hom を保持する。既存 Ind-S (9) の全族 Hom 回収要求は緩めず、下の型はその追加構成の最小検査型（各指定点で full native Hom 全体を回収）。一般の任意四面の可填性は要求しない。
- K-B への代入：X₀=元の core S 始域、X₁=同じ全 S 始域、X₂=元の零中間圏の core S、X₃=元の core S 終域。f は元の core 包含、g は同じ零値全 S 比較、h は元の第二短辺。f≫g の回収と T の二短辺の一致は既証明。同じ三面の厳密回収後だけ、既存の固定三面 fiber 内の比較と制御三角柱の利用側を使う。
- 採用経路：Ind-S (9b) の実三単体構成を K-6 c4 の F へ接続する。K-7 c5・d3 は同じ K-6 比較を消費し続ける。実供給までは条件付き。
- 固定 S・ν・K、I・P、採用済みの有限 BF 命題と共終性入力は変更しない。一般 BF 整流・一般 StableInfinity 上の K 関手化は再開しない。
- 以下は `lake env lean /tmp/kb-controlled-factorization-tetra-request.lean` で型検証成功。命題の証明・存在は主張しない。

```lean
import SerrePositivity.InfinityCategories.F1.Categories.CatInfinity
import SerrePositivity.InfinityCategories.F1.Coherent.CompositionTriangle
import SerrePositivity.InfinityCategories.F1.Coherent.Edges
import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

-- Supply specification, not an assumption or existence theorem.
def controlledFactorizationTetraFamilyRequest : Prop :=
  ∀ (X₀ X₁ X₂ X₃ : KanObject.{u})
    (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₃)
    (K : SSet.{u + 1}) (T : (Δ[2] : SSet.{u + 1}) ⊗ K ⟶ SpaceInfinity.{u}),
    (stdSimplex.δ (2 : Fin 3) ▷ K) ≫ T =
      fst (Δ[1] : SSet.{u + 1}) K ≫ SSet.yonedaEquiv.symm (coherentNerveEdge (f ≫ g)).edge →
    (stdSimplex.δ (0 : Fin 3) ▷ K) ≫ T =
      fst (Δ[1] : SSet.{u + 1}) K ≫ SSet.yonedaEquiv.symm (coherentNerveEdge h).edge →
    ∃ F : (Δ[3] : SSet.{u + 1}) ⊗ K ⟶ SpaceInfinity.{u},
      (stdSimplex.δ (0 : Fin 4) ▷ K) ≫ F =
        fst (Δ[2] : SSet.{u + 1}) K ≫
          SSet.yonedaEquiv.symm (coherentNerveCompStruct g h).simplex ∧
      (stdSimplex.δ (1 : Fin 4) ▷ K) ≫ F = T ∧
      (stdSimplex.δ (3 : Fin 4) ▷ K) ≫ F =
        fst (Δ[2] : SSet.{u + 1}) K ≫
          SSet.yonedaEquiv.symm (coherentNerveCompStruct f g).simplex ∧
      ∀ k : K _⦋0⦌,
        let t := SSet.yonedaEquiv (lift (𝟙 (Δ[3] : SSet.{u + 1})) (SSet.const k) ≫ F)
        let a := SSet.yonedaEquiv (lift (𝟙 (Δ[2] : SSet.{u + 1})) (SSet.const k) ≫ T)
        HEq ((SpaceInfinity.δ (2 : Fin 4) t).map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩)
          (a.map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩)
```
