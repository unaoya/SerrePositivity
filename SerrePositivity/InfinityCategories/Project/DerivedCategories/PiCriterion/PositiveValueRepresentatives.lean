module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.SphereClassPath
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.CoherentFilteredTotalDetection
public import SerrePositivity.KST.Spectra.FilteredLoopColimit

/-!
概要：全空間の正次数の類は、元の一つの値の類から実際の基点 path を経て得られる。
方針：有限球面の射として代表し、値検出の球面ホモトピーを指数 path へ転置する。
規約：両端の群の比較を一つの path 空間の類で示し、非相対単体ホモトピーで代用しない。
使われ方：filtered 余極限の全基点の元ごとの全射条件。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion
open KST.Spectra
variable {B : SSet.{u}} [Quasicategory B] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity B]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})

local notation "T" => _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKan F
local notation "V" b => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject
  (F.app (Opposite.op ⦋0⦌) (ULift.up b)))
local notation "j" b => _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.coherentDiagramValueToTotalKan F b

set_option maxHeartbeats 2000000 in
-- 複数の点つき対象の基点表示を含む存在型の elaboration に既定値以上を要する。
/-- 正次数の任意の類には、元の値内の代表と、両者を結ぶ実際の基点 path がある。 -/
lemma total_positiveClass_value_representative (n : ℕ) (x : T _⦋0⦌)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup T n (PointedSimplicialSet.ofVertex T x).basepoint) :
    ∃ b : B _⦋0⦌, ∃ y : (V b) _⦋0⦌,
      ∃ β : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (V b) n (PointedSimplicialSet.ofVertex (V b) y).basepoint,
      ∃ z : (KanPath.object T) _⦋0⦌,
      ∃ h₀ : (KanPath.evaluation T 0).app _ z =
        (PointedSimplicialSet.ofVertex T x).basepoint,
      ∃ h₁ : (KanPath.evaluation T 1).app _ z =
        (PointedSimplicialSet.ofVertex T
          ((j b).app _ (PointedSimplicialSet.ofVertex (V b) y).basepoint)).basepoint,
      ∃ hⱼ : (j b).app _ (PointedSimplicialSet.ofVertex (V b) y).basepoint =
        (PointedSimplicialSet.ofVertex T
          ((j b).app _ (PointedSimplicialSet.ofVertex (V b) y).basepoint)).basepoint,
      ∃ γ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (KanPath.object T) n z,
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (KanPath.evaluation T 0) h₀ γ = a ∧
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (KanPath.evaluation T 1) h₁ γ =
          _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (j b) hⱼ β := by
  let S := PointedSimplicialSet.sphere.{u} (n + 1)
  obtain ⟨f, hf⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.sphereClass_surjective (PointedSimplicialSet.ofVertex T x) n a
  obtain ⟨b, g, ⟨H⟩⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.coherentFilteredTotalKan_finite_value_detection F f.right
  let y := g.app _ S.basepoint
  let gp : S ⟶ PointedSimplicialSet.ofVertex (V b) y := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.pointedImageMap (A := S) g
  let p : PointedSimplicialSet.ofVertex (V b) y ⟶
      PointedSimplicialSet.ofVertex T
        ((j b).app _ (PointedSimplicialSet.ofVertex (V b) y).basepoint) :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.pointedImageMap (A := PointedSimplicialSet.ofVertex (V b) y) (j b)
  have H' : SSet.Homotopy f.right (gp ≫ p).right := H
  obtain ⟨z, h₀, h₁, γ, hγ₀, hγ₁⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.sphereClass_path_witness n x
    ((j b).app _ (PointedSimplicialSet.ofVertex (V b) y).basepoint) f (gp ≫ p) H'
  refine ⟨b, y, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.sphereClass n gp, z, h₀, h₁,
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint p, γ, hγ₀.trans hf, ?_⟩
  exact hγ₁.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.sphereClass_post n gp p).symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion
