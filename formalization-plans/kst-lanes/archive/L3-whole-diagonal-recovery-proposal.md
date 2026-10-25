# K-6 c4：Ind-S (9) の全パラメータ共有対角回収（仕様補足案・未採用）

概要：採用済みの全族 Hom 回収を、実四角柱の共有対角の厳密式へ接続するための型の補足。
方針：同じ encode・longHom に、直接 path の評価が再構成二胞体の実長辺全族を回収する式を添える。
規約：ユーザー判断待ち。Ind/F1 正本への供給仕様の補足案であり、本体の新しい存在仮定や証明済み成果には登録しない。(9b)・固定 S・ν・K、I・P は変更しない。
使われ方：同じ K=Δ[1] の実共有対角を、下側変形の全一単体と一致させて貼り合わせる。

- 現行 (9) は `encode ≫ longHom = 𝟙 L` と `∀ t : T₀, ∀ k : K₀, HEq ...` を要求する。後者は各 K 頂点での全 native Hom 写像を回収するが、K の非退化一単体に沿う共有対角の実辺そのものの等式を明記していない。
- `longHom` 自体が canonical な全族読出しであるという式も現行の存在命題にはない。切断式だけからこの読出しを canonical と同一視せず、点ごとの一致から `Δ[1] ⊗ K` 上の実辺の等式を推論しない。
- 補足案：既存の全族 Hom 回収・指定点の HEq・固定三面比較をすべて保持し、同じ `longHom` の直接 path 評価と、再構成二胞体の δ₁ 長辺全族との厳密等式を加える。一般 BF 整流や新しい商 API は含めない。
- 採用時：Ind-S (9) の仕様にこの式を追加依頼し、K-B の条件付き利用側では同じ強化命題を引数に取る。K-6 c4 の全時刻対角回収から c5・K-7 c5/d3 への接続を進める。
- 不採用時：現在の (9)/(9b) の利用側を保持し、同じ全時刻対角を得る別の証明が必要。固定三面比較・指定点の全 Hom 回収からの先は条件付きのまま。
- 下の全型は `lake env lean /tmp/kb-ind9-whole-diagonal-request.lean` で型検査済み。新しい対角条項は `∀ t : T _⦋0⦌` で始まるブロック。

```lean
import SerrePositivity.KST.Fibration.ZeroMiddleReconstructionSupply
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def indS9WholeDiagonalRequest : Prop :=
  ∀ (X Y Z : KanObject.{u}) (K : SSet.{u + 1})
    (f : K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom X Y))
    (g : K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom Y Z))
    (a : (Λ[2, 1] : SSet.{u + 1}) ⊗ K ⟶ SpaceInfinity.{u}),
    (horn₂₁.ι₀₁ ▷ K) ≫ a = (Δ[1] ◁ f) ≫
      intervalMappingUncurry (coherentHomIntervalComparison X Y) →
    (horn₂₁.ι₁₂ ▷ K) ≫ a = (Δ[1] ◁ g) ≫
      intervalMappingUncurry (coherentHomIntervalComparison Y Z) →
  let P := SimplicialThickening.Path
    (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3)) (ULift.up 2)
  let p : P :=
    { I := Set.univ
      left := Set.mem_univ _
      right := Set.mem_univ _
      left_le := fun k _ => Fin.zero_le k.down
      le_right := fun k _ => Fin.le_last k.down }
  let Pu := (SSet.uliftFunctor.{u + 1, u}).obj (nerve P)
  let H := (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom X Z)
  let c := lift f g ≫ (HomotopyLimits.uliftTensorIso.{u, u + 1}
    (SimplicialCategory.sHom X Y) (SimplicialCategory.sHom Y Z)).inv ≫
      (SSet.uliftFunctor.{u + 1, u}).map (eComp SSet.{u} X Y Z)
  let L := vertexFiber ((ihom K).map
    (evaluateFunctorAt (X := Pu) (Y := H) (ULift.up (ComposableArrows.mk₀ p))))
    (functorVertex c)
  let T := vertexFiber ((pre ((horn 2 (1 : Fin 3)).ι ▷ K)).app SpaceInfinity.{u})
    (functorVertex a)
  ∃ (encode : L ⟶ T) (longHom : T ⟶ L),
    encode ≫ longHom = 𝟙 L ∧
    (∀ (t : T _⦋0⦌) (k : K _⦋0⦌),
      let Lt := (functorVertexEquiv K ((ihom Pu).obj H)).symm
        ((longHom.app (Opposite.op ⦋0⦌) t).val)
      let Tt := (functorVertexEquiv (Δ[2] ⊗ K) SpaceInfinity.{u}).symm t.val
      let s := SSet.yonedaEquiv ((functorVertexEquiv Δ[2] SpaceInfinity.{u}).symm
        ((curry Tt).app (Opposite.op ⦋0⦌) k))
      HEq (Lt.app (Opposite.op ⦋0⦌) k)
        (functorVertex ((SSet.uliftFunctor.{u + 1, u}).map
          (s.map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩)))) ∧
    (∀ t : T _⦋0⦌,
      let direct : P :=
        { I := {ULift.up 0, ULift.up 2}
          left := by simp
          right := by simp
          left_le := fun k _ => Fin.zero_le k.down
          le_right := fun k _ => Fin.le_last k.down }
      let Lt := (functorVertexEquiv K ((ihom Pu).obj H)).symm
        ((longHom.app (Opposite.op ⦋0⦌) t).val)
      let Tt := (functorVertexEquiv (Δ[2] ⊗ K) SpaceInfinity.{u}).symm t.val
      (stdSimplex.δ (1 : Fin 3) ▷ K) ≫ Tt =
        (Δ[1] ◁ (Lt ≫ evaluateFunctorAt
          (X := Pu) (Y := H) (ULift.up (ComposableArrows.mk₀ direct)))) ≫
            intervalMappingUncurry (coherentHomIntervalComparison X Z)) ∧
    (∀ b : (Λ[3, 2] : SSet.{u + 1}) ⊗ K ⟶ SpaceInfinity.{u},
      let E := vertexFiber ((pre ((horn 3 (2 : Fin 4)).ι ▷ K)).app SpaceInfinity.{u})
        (functorVertex b)
      IsContractibleKan E ∧ ∀ old controlled : E _⦋0⦌,
        Nonempty (VertexIso old controlled))
```
