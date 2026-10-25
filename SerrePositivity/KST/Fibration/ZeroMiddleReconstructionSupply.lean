module
public import SerrePositivity.InfinityCategories.F1.Categories.CatInfinity
public import SerrePositivity.InfinityCategories.F1.Diagrams.CompositionTriangleFamily
public import SerrePositivity.InfinityCategories.Core.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Core.EquivalencePath
public import SerrePositivity.InfinityCategories.F1.Coherent.HomIntervalNaturality
public import SerrePositivity.InfinityCategories.Core.UniverseSSetMaps
public import SerrePositivity.InfinityCategories.F1.Coherent.CompositionTriangle
public import SerrePositivity.InfinityCategories.F1.Coherent.Edges
public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits

/-!
概要：ユーザー採用の Ind-S (9)・(9b) の供給命題を、利用側の明示引数の型として保持する。
方針：全族再構成と因子分解三単体族の仕様を分け、供給後に同じ型へ代入する。
規約：存在・証明済み成果は主張せず、F1 の汎用構成をここで証明しない。
使われ方：K-6 c4 の未供給命題に条件付きの消費と、その K-7 への接続。
-/
@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.KST.Fibration

/-- 概要：指定短辺・合成端・全長 Hom を保持する全族再構成の供給命題。
方針：採用済み Ind-S (9) の encode・longHom と固定三面比較をそのまま型にする。
規約：命題の証明や主経路の新しい存在仮定は追加しない。
使われ方：供給前の再構成利用側の明示定理引数。 -/
def zeroMiddleControlledTriangleSupply : Prop :=
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

/-- 概要：元の二胞体と二つの合成面を保つ因子分解三単体族の供給命題。
方針：採用済み Ind-S (9b) の三面回収と欠面の指定点の全 native Hom 回収を保持する。
規約：全族 Hom 回収を弱める代替物や任意四面の充填性として使わない。
使われ方：構成済み三単体族を同じ固定三面 fiber の比較へ渡す。 -/
def zeroMiddleFactorizationTetraSupply : Prop :=
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

end SerrePositivity.KST.Fibration
