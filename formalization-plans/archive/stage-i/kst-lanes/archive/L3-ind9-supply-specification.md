# Ind-S (9) 採用済み仕様型の保管

以下は供給依頼時の正規化後仕様型。実供給は F1 の controlledTriangleNormalizedFamilySupply（f206fbbb1）と controlledFactorizationTetraFamily（77a33b4c9）を読む。厳密切断や元の未正規化 t 自身の全対角回収は要求しない。

### Ind-S (9)：指定全長 Hom の全族再構成の供給型（採用（06:29））
- (9)・(9b) はユーザー採用（06:29）、一括で Ind-S に発注済み。以下は F1 新規葉への仕様命題の型であり、主経路の新しい存在仮定ではない。`K` は任意の単体集合。二短辺 `f`・`g` も指定全族として固定し、全ホーン族 `a` はその標準 coherent 区間像を厳密に回収する。
- `c` は同じ全短辺族の元の豊穣合成。`L` は合成端を全入力で `c` に固定した全長 Hom 族の空間、`T` は同じ全ホーン `a` を固定した二胞体族の実延長空間。`encode ≫ longHom` と恒等の全族可逆比較を保持する。厳密切断は有限反例により撤回（ユーザー採用）。読出しは各指定入力点で元の全豊穣 Hom に一致する。
- K-B では元の全 S• Hom を core 包含で制限してから渡す。未制限の全 S• Hom は始域が異なる。末尾の比較は同じ三面 `b` を固定する実充填空間内で取り、制御充填を実際に構成してから既存充填と比較する。任意四面の可填性を境界一致だけから要求しない。
```lean
import SerrePositivity.InfinityCategories.F1.Categories.CatInfinity
import SerrePositivity.InfinityCategories.F1.Diagrams.CompositionTriangleFamily
import SerrePositivity.InfinityCategories.Core.FunctorEvaluation
import SerrePositivity.InfinityCategories.Core.EquivalencePath
import SerrePositivity.InfinityCategories.F1.Coherent.HomIntervalNaturality
import SerrePositivity.InfinityCategories.Core.UniverseSSetMaps
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

-- Supply specification only; no existence assumption in the main route.
def indS9ControlledTriangleFamilyRequest : Prop :=
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
    Nonempty (FunctorIso (encode ≫ longHom) (𝟙 L)) ∧
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


