module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.BridgeComponents
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.BridgePositiveInjectivity
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.BridgePositiveSurjectivity
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.KanMapCriterion

/-!
概要：D の元ごとの条件を、有限検出される Kan 模型の比較射の全基点 π 判定へ渡す。
方針：脚・transition の実ホモトピーから零次数を計算し、正次数の両方向を合成する。
規約：D の構造を直接消費し、幾何的な有限検出と実可換性は明示する。
使われ方：元の coherent 全空間余錐への特殊化と宇宙移送。
-/

@[expose] public section
noncomputable section
universe u w
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion
open KST.Spectra

/-- 有限検出・元の脚との Homotopy・段階の Homotopy を持つ比較は D の条件から π 同型。 -/
lemma bridge_finite_piCriterion {I : Type u} [PartialOrder I]
    (X : I → _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{w}) (A T : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{w})
    (τ : ∀ {i j : I}, i ≤ j → ((X i).obj ⟶ (X j).obj))
    (l : ∀ i : I, (X i).obj ⟶ A.obj)
    (h : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.DGBarCompactSpacePiData X A τ l)
    (s : ∀ i : I, (X i).obj ⟶ T.obj) (q : T.obj ⟶ A.obj)
    (hcomm : ∀ i : I, Nonempty (Homotopy (l i) (s i ≫ q)))
    (hstage : ∀ (i j : I) (hij : i ≤ j), Nonempty (Homotopy (s i) (τ hij ≫ s j)))
    (hfinite : ∀ {K : SSet.{w}} [K.Finite] (f : K ⟶ T.obj),
      ∃ i : I, ∃ g : K ⟶ (X i).obj, Nonempty (Homotopy f (g ≫ s i))) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.KanMapPiCriterion q := by
  constructor
  · apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.bridge_mapPiZero_bijective X A T τ l h s q
    · intro i y
      obtain ⟨H⟩ := hcomm i
      exact (π₀.sound (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H y)).symm
    · intro i j hij y
      obtain ⟨H⟩ := hstage i j hij
      exact (π₀.sound (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H y)).symm
    · intro x
      obtain ⟨i, y, _, z, h₀, h₁, _, _⟩ :=
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.finite_positive_pair_representative X T.obj s hfinite 0 x ![1, 1]
      obtain ⟨e, _⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.pathVertexEdge_exists z h₀ h₁
      exact ⟨i, y, (π₀.sound e).symm⟩
  · intro x n
    exact ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.bridge_positive_injective X A T τ l h s q hcomm hstage hfinite n x,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.bridge_positive_surjective X A T τ l h s q hcomm hstage hfinite n x⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion
