module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.TransformationFamilyDiagram
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.F1DiagramsTrianglePrism

/-!
概要：合成可能な coherent な変換の族を三角形の族へ延長する。
方針：積の底上の図式として二辺を貼り、空間の ∞ 圏で内ホーンを充填する。
規約：底の充填性とパラメーターの小ささは不要。
使われ方：straightening の写像空間比較の全高次パラメーターでの合成。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

/-- 概要：変換の族へ curry して戻した図式は元の区間図式そのもの。
方針：結合子を相殺して既存の prism 公式を使う。
規約：両端はパラメーターに関して定値。
使われ方：三角形の長辺を変換空間への射として表示する。 -/
lemma coherentTransformationFamilyDiagram_curryOfEndpoints {B K : SSet.{u + 1}}
    (F G : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (H : (Δ[1] : SSet.{u + 1}) ⊗ (B ⊗ K) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (B ⊗ K) ≫ H = fst B K ≫ F)
    (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (B ⊗ K) ≫ H = fst B K ≫ G) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTransformationFamilyDiagram (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.coherentTransformationFamilyCurry F G H h₀ h₁) = H := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTransformationFamilyDiagram, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.coherentTransformationFamilyCurry_prism]
  simp only [Iso.inv_hom_id_assoc]

/-- 概要：合成可能な二つの変換の族は長辺と coherent な三角形の族を持つ。
方針：空間の ∞ 圏の内ホーンを全パラメーター上で充填し長辺を curry する。
規約：選択した長辺の厳密な結合性は主張しない。
使われ方：一般の表現間の相対射の族の合成を同時に実現する。 -/
lemma coherentTransformationFamilyTriangle_nonempty {B K : SSet.{u + 1}}
    {F G J : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}}
    (t₀₁ : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationSpace F G)
    (t₁₂ : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationSpace G J) :
    ∃ (t₀₂ : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationSpace F J)
      (H : (Δ[2] : SSet.{u + 1}) ⊗ (B ⊗ K) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}),
      (stdSimplex.δ (2 : Fin 3) ▷ (B ⊗ K)) ≫ H =
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTransformationFamilyDiagram t₀₁ ∧
      (stdSimplex.δ (0 : Fin 3) ▷ (B ⊗ K)) ≫ H =
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTransformationFamilyDiagram t₁₂ ∧
      (stdSimplex.δ (1 : Fin 3) ▷ (B ⊗ K)) ≫ H =
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTransformationFamilyDiagram t₀₂ := by
  have hw : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (B ⊗ K) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTransformationFamilyDiagram t₀₁ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (B ⊗ K) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTransformationFamilyDiagram t₁₂ := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTransformationFamilyDiagram_one, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTransformationFamilyDiagram_zero]
  obtain ⟨H, h₀₁, h₁₂, _⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.innerFibration_fillTrianglePrism
    (terminal.from _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTransformationFamilyDiagram t₀₁)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTransformationFamilyDiagram t₁₂) (terminal.from _) hw
    (Subsingleton.elim _ _) (Subsingleton.elim _ _)
  let L := (stdSimplex.δ (1 : Fin 3) ▷ (B ⊗ K)) ≫ H
  have hz : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (B ⊗ K) ≫ (stdSimplex.δ (1 : Fin 3) ▷ (B ⊗ K)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (B ⊗ K) ≫ (stdSimplex.δ (2 : Fin 3) ▷ (B ⊗ K)) := rfl
  have ho : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (B ⊗ K) ≫ (stdSimplex.δ (1 : Fin 3) ▷ (B ⊗ K)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (B ⊗ K) ≫ (stdSimplex.δ (0 : Fin 3) ▷ (B ⊗ K)) := rfl
  have hL₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (B ⊗ K) ≫ L = fst B K ≫ F := by
    dsimp only [L]
    rw [← Category.assoc, hz, Category.assoc, h₀₁,
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTransformationFamilyDiagram_zero]
  have hL₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (B ⊗ K) ≫ L = fst B K ≫ J := by
    dsimp only [L]
    rw [← Category.assoc, ho, Category.assoc, h₁₂,
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTransformationFamilyDiagram_one]
  refine ⟨_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.coherentTransformationFamilyCurry F J L hL₀ hL₁, H, h₀₁, h₁₂, ?_⟩
  exact (coherentTransformationFamilyDiagram_curryOfEndpoints F J L hL₀ hL₁).symm

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
