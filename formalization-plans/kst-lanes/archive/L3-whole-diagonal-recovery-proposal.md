# K-6 c4：正規化後の全族共有対角回収（採用済み仕様）

概要：採用済みの全族 Hom 回収を、正規化後の実四角柱の共有対角の厳密式へ接続する。
方針：normalize(t)=encode(longHom(t)) の直接 path 評価を実長辺全族へ厳密回収し、元 t へは固定ホーン内の可逆比較で戻す。
規約：Ind-S の設計判断をユーザー採用。元 t 自身への全対角の厳密等式は偽なので要求しない。旧 (9)・(9b) の条項、固定 S・ν・K、I・P は保持する。
使われ方：同じ K=Δ[1] の実共有対角を下側変形の全一単体へ貼り合わせる。

- encode ≫ longHom = 𝟙 L と各指定点の全 native Hom 回収は不変。追加対角条項の対象を元 t から normalize(t) に変更し、同じ固定ホーン fiber T 内の VertexIso t normalize(t) をあわせて要求する。
- K-B の実再構成族 encode(ℓ) は正規化不変なので、共有対角の全族厳密回収を保つ。ZeroMiddleNormalizedFamily は読出し保存・冪等性・固定ホーン内同型を回収し、実全族の FunctorIso にして元へ戻す。
- 命題の存在は主張しない。現在の型の正本は ZeroMiddleReconstructionSupply.lean。以下の型は同じ定義を表示したもので、/tmp/kb-ind9-normalized-diagonal-request.lean にも保存する。

```lean
import SerrePositivity.KST.Fibration.ZeroMiddleReconstructionSupply
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def indS9NormalizedDiagonalRequest : Prop :=
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
      let nt := encode.app (Opposite.op ⦋0⦌) (longHom.app (Opposite.op ⦋0⦌) t)
      let Tt := (functorVertexEquiv (Δ[2] ⊗ K) SpaceInfinity.{u}).symm nt.val
      (stdSimplex.δ (1 : Fin 3) ▷ K) ≫ Tt =
        (Δ[1] ◁ (Lt ≫ evaluateFunctorAt
          (X := Pu) (Y := H) (ULift.up (ComposableArrows.mk₀ direct)))) ≫
            intervalMappingUncurry (coherentHomIntervalComparison X Z)) ∧
    (∀ t : T _⦋0⦌, Nonempty (VertexIso t
      (encode.app (Opposite.op ⦋0⦌) (longHom.app (Opposite.op ⦋0⦌) t)))) ∧
    (∀ b : (Λ[3, 2] : SSet.{u + 1}) ⊗ K ⟶ SpaceInfinity.{u},
      let E := vertexFiber ((pre ((horn 3 (2 : Fin 4)).ι ▷ K)).app SpaceInfinity.{u})
        (functorVertex b)
      IsContractibleKan E ∧ ∀ old controlled : E _⦋0⦌,
        Nonempty (VertexIso old controlled))
```
