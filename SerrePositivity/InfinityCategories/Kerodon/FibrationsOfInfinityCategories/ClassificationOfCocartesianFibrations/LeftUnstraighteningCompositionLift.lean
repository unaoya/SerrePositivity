module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftUnstraighteningSelectedLift
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.F1DiagramsTrianglePrism

/-!
概要：coherent な三角形の二辺に対する unstraightening の射の合成の具体的な持ち上げ。
方針：二つの選択した prism を貼り、内ホーンの積を充填して長辺を取る。
規約：三角形の族と底への射影を厳密に固定する。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、unstraightening の変換の合成則。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：三角形の族の辺への制限はパラメーターの射による前合成と可換。
方針：テンソルの二因子の射の交換則を使う。
規約：i は欠ける頂点の番号。
使われ方：Kerodon Proposition 5.2.5.1（Tag 01VU）、パラメーター付き三角形の持ち上げの底。 -/
lemma trianglePrism_restrict_baseChange {A B X : SSet.{u}}
    (p : A ⟶ B) (T : (Δ[2] : SSet.{u}) ⊗ B ⟶ X) (i : Fin 3) :
    (stdSimplex.δ i ▷ A) ≫ ((Δ[2] ◁ p) ≫ T) =
      (Δ[1] ◁ p) ≫ ((stdSimplex.δ i ▷ B) ≫ T) := by
  rw [← whisker_exchange_assoc]

/-- 概要：coherent な三角形の二辺の選択した unstraightening の射の合成は長辺の持ち上げの終点になる。
方針：後半の prism を前半の射で引き戻し、二つの prism を三角形に延長する。
規約：長辺の射の選択との比較は後続の終点の同型で行う。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、変換の合成の具体的な証人。 -/
lemma exists_leftUnstraighteningTransformationComposite_lift
    {B : SSet.{u + 1}} (F G J : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (α β γ : (Δ[1] : SSet.{u + 1}) ⊗ B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (hα₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 B ≫ α = F) (hα₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 B ≫ α = G)
    (hβ₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 B ≫ β = G) (hβ₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 B ≫ β = J)
    (T : (Δ[2] : SSet.{u + 1}) ⊗ B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (hTα : (stdSimplex.δ (2 : Fin 3) ▷ B) ≫ T = α)
    (hTβ : (stdSimplex.δ (0 : Fin 3) ▷ B) ≫ T = β)
    (hTγ : (stdSimplex.δ (1 : Fin 3) ▷ B) ≫ T = γ) :
    ∃ W : (Δ[1] : SSet.{u + 1}) ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraightening F ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity.{u},
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ W = pullback.fst _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection F ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ W =
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationMap F G α hα₀ hα₁).val ≫
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationMap G J β hβ₀ hβ₁).val) ≫
            pullback.fst _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection J ∧
      W ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection = (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection F) ≫ γ := by
  let f := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationMap F G α hα₀ hα₁).val
  let g := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationMap G J β hβ₀ hβ₁).val
  have hf : f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection G = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection F :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationMap F G α hα₀ hα₁).property
  obtain ⟨W₀₁, hW₀, hW₁, hWp⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.exists_leftUnstraighteningTransformationMap_lift F G α hα₀ hα₁
  obtain ⟨W₁₂, hV₀, hV₁, hVp⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.exists_leftUnstraighteningTransformationMap_lift G J β hβ₀ hβ₁
  let A := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraightening F
  let V := (Δ[1] ◁ f) ≫ W₁₂
  let t := (Δ[2] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection F) ≫ T
  have hw : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ W₀₁ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ V := by
    dsimp only [V]
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc, hV₀, hW₁]
  have hp₀₁ : W₀₁ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection = (stdSimplex.δ (2 : Fin 3) ▷ A) ≫ t := by
    rw [hWp, trianglePrism_restrict_baseChange, hTα]
  have hp₁₂ : V ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection = (stdSimplex.δ (0 : Fin 3) ▷ A) ≫ t := by
    dsimp only [V]
    rw [Category.assoc, hVp, ← Category.assoc, ← MonoidalCategory.whiskerLeft_comp, hf,
      trianglePrism_restrict_baseChange, hTβ]
  obtain ⟨S, hS₀₁, hS₁₂, hSp⟩ :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.innerFibration_fillTrianglePrism _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection W₀₁ V t hw hp₀₁ hp₁₂
  let W := (stdSimplex.δ (1 : Fin 3) ▷ A) ≫ S
  have hz : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ (stdSimplex.δ (1 : Fin 3) ▷ A) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ (stdSimplex.δ (2 : Fin 3) ▷ A) := rfl
  have ho : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ (stdSimplex.δ (1 : Fin 3) ▷ A) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ (stdSimplex.δ (0 : Fin 3) ▷ A) := rfl
  refine ⟨W, ?_, ?_, ?_⟩
  · dsimp only [W]
    rw [← Category.assoc, hz, Category.assoc, hS₀₁]
    exact hW₀
  · dsimp only [W]
    rw [← Category.assoc, ho, Category.assoc, hS₁₂]
    dsimp only [V]
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc, hV₁, ← Category.assoc]
  · dsimp only [W]
    rw [Category.assoc, hSp, trianglePrism_restrict_baseChange, hTγ]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
