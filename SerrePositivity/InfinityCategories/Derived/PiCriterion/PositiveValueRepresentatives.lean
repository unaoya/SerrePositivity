module

public import SerrePositivity.InfinityCategories.Derived.PiCriterion.SphereClassPath
public import SerrePositivity.InfinityCategories.F2.Filtered.CoherentFilteredTotalDetection
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
namespace SerrePositivity.InfinityCategories.F2.PiCriterion
open KST.Spectra
variable {B : SSet.{u}} [Quasicategory B] [IsFilteredInfinity B]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})

local notation "T" => coherentDiagramTotalKan F
local notation "V" b => KanObject.obj (spaceInfinityObject
  (F.app (Opposite.op ⦋0⦌) (ULift.up b)))
local notation "j" b => coherentDiagramValueToTotalKan F b

set_option maxHeartbeats 2000000 in
-- 複数の点つき対象の基点表示を含む存在型の elaboration に既定値以上を要する。
/-- 正次数の任意の類には、元の値内の代表と、両者を結ぶ実際の基点 path がある。 -/
lemma total_positiveClass_value_representative (n : ℕ) (x : T _⦋0⦌)
    (a : KanHomotopyGroup T n (PointedSimplicialSet.ofVertex T x).basepoint) :
    ∃ b : B _⦋0⦌, ∃ y : (V b) _⦋0⦌,
      ∃ β : KanHomotopyGroup (V b) n (PointedSimplicialSet.ofVertex (V b) y).basepoint,
      ∃ z : (KanPath.object T) _⦋0⦌,
      ∃ h₀ : (KanPath.evaluation T 0).app _ z =
        (PointedSimplicialSet.ofVertex T x).basepoint,
      ∃ h₁ : (KanPath.evaluation T 1).app _ z =
        (PointedSimplicialSet.ofVertex T
          ((j b).app _ (PointedSimplicialSet.ofVertex (V b) y).basepoint)).basepoint,
      ∃ hⱼ : (j b).app _ (PointedSimplicialSet.ofVertex (V b) y).basepoint =
        (PointedSimplicialSet.ofVertex T
          ((j b).app _ (PointedSimplicialSet.ofVertex (V b) y).basepoint)).basepoint,
      ∃ γ : KanHomotopyGroup (KanPath.object T) n z,
        KanHomotopyGroup.map (KanPath.evaluation T 0) h₀ γ = a ∧
        KanHomotopyGroup.map (KanPath.evaluation T 1) h₁ γ =
          KanHomotopyGroup.map (j b) hⱼ β := by
  let S := PointedSimplicialSet.sphere.{u} (n + 1)
  obtain ⟨f, hf⟩ := sphereClass_surjective (PointedSimplicialSet.ofVertex T x) n a
  obtain ⟨b, g, ⟨H⟩⟩ := coherentFilteredTotalKan_finite_value_detection F f.right
  let y := g.app _ S.basepoint
  let gp : S ⟶ PointedSimplicialSet.ofVertex (V b) y := pointedImageMap (A := S) g
  let p : PointedSimplicialSet.ofVertex (V b) y ⟶
      PointedSimplicialSet.ofVertex T
        ((j b).app _ (PointedSimplicialSet.ofVertex (V b) y).basepoint) :=
    pointedImageMap (A := PointedSimplicialSet.ofVertex (V b) y) (j b)
  have H' : SSet.Homotopy f.right (gp ≫ p).right := H
  obtain ⟨z, h₀, h₁, γ, hγ₀, hγ₁⟩ := sphereClass_path_witness n x
    ((j b).app _ (PointedSimplicialSet.ofVertex (V b) y).basepoint) f (gp ≫ p) H'
  refine ⟨b, y, sphereClass n gp, z, h₀, h₁,
    OmegaSpectrum.pointedMap_basepoint p, γ, hγ₀.trans hf, ?_⟩
  exact hγ₁.trans (sphereClass_post n gp p).symm

end SerrePositivity.InfinityCategories.F2.PiCriterion
