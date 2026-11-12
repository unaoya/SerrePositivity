module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftUnstraighteningEdgeLiftFamily
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorExtensionEndpoint
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PrismLiftSpace

/-!
概要：任意の始域からの pointed 区間族を、元の unstraightening の辺の作用と相対的に比較する。
方針：元の全写像空間の族を始域へ制限し、同じ始点と底を持つ延長の可縮性を使う。
規約：比較は底を固定した相対写像空間の頂点同型であり、点ごとの同型ではない。
使われ方：G8 の四角形①で要素の圏の区間族から relativePreIso の入力を構成する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations

/-- 同じ始点と底を持つ実区間族の終点は、元の辺の作用を制限した射と相対写像空間内で同型。 -/
def leftUnstraighteningRestrictedWitnessIso {A B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u})
    (e : SSet.Edge (X := (ihom B).obj SpaceInfinity.{u}) (functorVertex F) (functorVertex G))
    (a : A ⟶ B) (j : A ⟶ leftUnstraightening F)
    (hj : j ≫ leftUnstraighteningProjection F = a)
    (W : (Δ[1] : SSet.{u + 1}) ⊗ A ⟶ PointedSpaceInfinity.{u})
    (hW₀ : prismEndpoint 0 A ≫ W = j ≫ pullback.fst pointedSpaceProjection F)
    (hWp : W ≫ pointedSpaceProjection = (Δ[1] ◁ a) ≫ functorEdgePrism e)
    (g : A ⟶ leftUnstraightening G) (hg : g ≫ leftUnstraighteningProjection G = a)
    (hW₁ : prismEndpoint 1 A ≫ W = g ≫ pullback.fst pointedSpaceProjection G) :
    VertexIso
      (relativeFunctorVertex (leftUnstraighteningProjection G) a
        (j ≫ leftUnstraighteningEdgeLiftMap F G e) (by
          rw [Category.assoc, leftUnstraighteningEdgeLiftMap_projection, hj]))
      (relativeFunctorVertex (leftUnstraighteningProjection G) a g hg) := by
  let b := (Δ[1] ◁ a) ≫ functorEdgePrism e
  let v := j ≫ pullback.fst pointedSpaceProjection F
  let V := (Δ[1] ◁ j) ≫ leftUnstraighteningEdgeLiftFamily F G e
  have hv : v ≫ pointedSpaceProjection = prismEndpoint 0 A ≫ b := by
    dsimp only [v, b]
    rw [Category.assoc, pullback.condition]
    change j ≫ leftUnstraighteningProjection F ≫ F = _
    rw [← Category.assoc, hj, ← Category.assoc, prismEndpoint_naturality,
      Category.assoc, functorEdgePrism_zero]
  have hV : V ≫ pointedSpaceProjection = b := by
    dsimp only [V, b]
    rw [Category.assoc, leftUnstraighteningEdgeLiftFamily_projection,
      ← Category.assoc, ← MonoidalCategory.whiskerLeft_comp, hj]
  have hV₀ : prismEndpoint 0 A ≫ V = v := by
    dsimp only [V, v]
    rw [← Category.assoc, prismEndpoint_naturality, Category.assoc,
      leftUnstraighteningEdgeLiftFamily_zero]
  have hV₁ : prismEndpoint 1 A ≫ V =
      (j ≫ leftUnstraighteningEdgeLiftMap F G e) ≫ pullback.fst pointedSpaceProjection G := by
    dsimp only [V]
    rw [← Category.assoc, prismEndpoint_naturality, Category.assoc,
      leftUnstraighteningEdgeLiftFamily_one, Category.assoc]
  have hb₁ : prismEndpoint 1 A ≫ b = a ≫ G := by
    dsimp only [b]
    rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, functorEdgePrism_one]
  exact relativeFunctorExtensionEndpoint_witnessIso pointedSpaceProjection b
    (prismEndpoint 0 A) (prismEndpoint_zero_leftAnodyne A) v hv
    (prismEndpoint 1 A) G a hb₁ V W hV hWp hV₀ hW₀
    (j ≫ leftUnstraighteningEdgeLiftMap F G e) g
    (by change (j ≫ leftUnstraighteningEdgeLiftMap F G e) ≫ leftUnstraighteningProjection G = a
        rw [Category.assoc, leftUnstraighteningEdgeLiftMap_projection, hj]) hg hV₁ hW₁

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
