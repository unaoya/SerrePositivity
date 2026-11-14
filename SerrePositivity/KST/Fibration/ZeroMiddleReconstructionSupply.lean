module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CompositionTriangleFamily
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePath
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.HomIntervalNaturality
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.UniverseSSetMaps
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.CompositionTriangle
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Edges
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
def zeroMiddleControlledTriangleSupplyWith
    (comparison : ∀ (A : SSet.{u + 1}), (A ⟶ A) → Prop) : Prop :=
  ∀ (X Y Z : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) (K : SSet.{u + 1})
    (f : K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom X Y))
    (g : K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom Y Z))
    (a : (Λ[2, 1] : SSet.{u + 1}) ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}),
    (horn₂₁.ι₀₁ ▷ K) ≫ a = (Δ[1] ◁ f) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison X Y) →
    (horn₂₁.ι₁₂ ▷ K) ≫ a = (Δ[1] ◁ g) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison Y Z) →
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
  let c := lift f g ≫ (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso.{u, u + 1}
    (SimplicialCategory.sHom X Y) (SimplicialCategory.sHom Y Z)).inv ≫
      (SSet.uliftFunctor.{u + 1, u}).map (eComp SSet.{u} X Y Z)
  let L := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber ((ihom K).map
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (X := Pu) (Y := H) (ULift.up (ComposableArrows.mk₀ p))))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex c)
  let T := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber ((pre ((horn 2 (1 : Fin 3)).ι ▷ K)).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a)
  ∃ (encode : L ⟶ T) (longHom : T ⟶ L),
    comparison L (encode ≫ longHom) ∧
    (∀ (t : T _⦋0⦌) (k : K _⦋0⦌),
      let Lt := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv K ((ihom Pu).obj H)).symm
        ((longHom.app (Opposite.op ⦋0⦌) t).val)
      let Tt := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (Δ[2] ⊗ K) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}).symm t.val
      let s := SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv Δ[2] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}).symm
        ((curry Tt).app (Opposite.op ⦋0⦌) k))
      HEq (Lt.app (Opposite.op ⦋0⦌) k)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{u + 1, u}).map
          (s.map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩)))) ∧
    (∀ t : T _⦋0⦌,
      let direct : P :=
        { I := {ULift.up 0, ULift.up 2}
          left := by simp
          right := by simp
          left_le := fun k _ => Fin.zero_le k.down
          le_right := fun k _ => Fin.le_last k.down }
      let Lt := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv K ((ihom Pu).obj H)).symm
        ((longHom.app (Opposite.op ⦋0⦌) t).val)
      let nt := encode.app (Opposite.op ⦋0⦌) (longHom.app (Opposite.op ⦋0⦌) t)
      let Tt := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (Δ[2] ⊗ K) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}).symm nt.val
      (stdSimplex.δ (1 : Fin 3) ▷ K) ≫ Tt =
        (Δ[1] ◁ (Lt ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
          (X := Pu) (Y := H) (ULift.up (ComposableArrows.mk₀ direct)))) ≫
            _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison X Z)) ∧
    (∀ t : T _⦋0⦌, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso t
      (encode.app (Opposite.op ⦋0⦌) (longHom.app (Opposite.op ⦋0⦌) t)))) ∧
    (∀ b : (Λ[3, 2] : SSet.{u + 1}) ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u},
      let E := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber ((pre ((horn 3 (2 : Fin 4)).ι ▷ K)).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex b)
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan E ∧ ∀ old controlled : E _⦋0⦌,
        Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso old controlled))

/-- 概要：旧仕様の厳密切断に条件付きの再構成命題を保持する。
方針：共通仕様の比較条項を厳密等式へ特殊化する。
規約：この仕様の実供給は要求しない。採用済み経路は可逆比較版を使う。
使われ方：旧条件付き定理の型と証明の保存。 -/
def zeroMiddleControlledTriangleSupply : Prop :=
  zeroMiddleControlledTriangleSupplyWith.{u} (fun A e => e = 𝟙 A)

/-- 概要：厳密切断を要求せず全族の可逆比較で長 Hom を回収する採用済み供給命題。
方針：同じ二短辺・native Hom 回収・正規化対角・固定ホーン内同型を保持する。
規約：存在は主張しない。比較は長 Hom 族の空間上の全関手同型である。
使われ方：K-6 c4 の新仕様に条件付きの正規化と可逆移送。 -/
def zeroMiddleControlledTriangleComparisonSupply : Prop :=
  zeroMiddleControlledTriangleSupplyWith.{u}
    (fun A e => Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso e (𝟙 A)))

/-- 概要：元の二胞体と二つの合成面を保つ因子分解三単体族の供給命題。
方針：採用済み Ind-S (9b) の三面回収と欠面の指定点の全 native Hom 回収を保持する。
規約：全族 Hom 回収を弱める代替物や任意四面の充填性として使わない。
使われ方：構成済み三単体族を同じ固定三面 fiber の比較へ渡す。 -/
def zeroMiddleFactorizationTetraSupply : Prop :=
  ∀ (X₀ X₁ X₂ X₃ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u})
    (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₃)
    (K : SSet.{u + 1}) (T : (Δ[2] : SSet.{u + 1}) ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}),
    (stdSimplex.δ (2 : Fin 3) ▷ K) ≫ T =
      fst (Δ[1] : SSet.{u + 1}) K ≫ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (f ≫ g)).edge →
    (stdSimplex.δ (0 : Fin 3) ▷ K) ≫ T =
      fst (Δ[1] : SSet.{u + 1}) K ≫ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge h).edge →
    ∃ F : (Δ[3] : SSet.{u + 1}) ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u},
      (stdSimplex.δ (0 : Fin 4) ▷ K) ≫ F =
        fst (Δ[2] : SSet.{u + 1}) K ≫
          SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct g h).simplex ∧
      (stdSimplex.δ (1 : Fin 4) ▷ K) ≫ F = T ∧
      (stdSimplex.δ (3 : Fin 4) ▷ K) ≫ F =
        fst (Δ[2] : SSet.{u + 1}) K ≫
          SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct f g).simplex ∧
      ∀ k : K _⦋0⦌,
        let t := SSet.yonedaEquiv (lift (𝟙 (Δ[3] : SSet.{u + 1})) (SSet.const k) ≫ F)
        let a := SSet.yonedaEquiv (lift (𝟙 (Δ[2] : SSet.{u + 1})) (SSet.const k) ≫ T)
        HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.δ (2 : Fin 4) t).map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩)
          (a.map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩)

end SerrePositivity.KST.Fibration
