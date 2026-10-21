module

public import SerrePositivity.KST.LocalizingInvariants.SquareFrameFunctoriality
public import SerrePositivity.KST.LocalizingInvariants.EquivalencePathFamily
public import SerrePositivity.InfinityCategories.Stable.SquareFunctorTransport

/-!
概要：元の正方形の境界に指定された四辺の可逆 path を、正方形全体へ延長する。
方針：path の始点評価の自明 Kan 性と境界の単射性を使う。
規約：指定した境界 path は厳密に保持。使われ方：元の BF 合成射への四辺の移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.SquareFrame
variable {X : SSet.{u}} [Quasicategory X] (f : SquareFrame (equivalencePath X))
  (Q : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X)
  (hf : f.postcomp (equivalencePathEndpoint X 0) = ofSquare Q)

structure PathExtension where
  family : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ equivalencePath X
  source : family ≫ equivalencePathEndpoint X 0 = Q
  boundary : boundaryι ≫ family = f.diagram

include hf in
lemma pathExtension_nonempty : Nonempty (PathExtension f Q) := by
  have he : f.diagram ≫ equivalencePathEndpoint X 0 = boundaryι ≫ Q := by
    rw [diagram_postcomp, hf, diagram_ofSquare]
  let sq : CommSq f.diagram boundaryι (equivalencePathEndpoint X 0) Q := ⟨he⟩
  have : HasLiftingProperty boundaryι (equivalencePathEndpoint X 0) :=
    TrivialKanFibration.mem (p := equivalencePathEndpoint X 0) boundaryι inferInstance
  exact ⟨⟨sq.lift, sq.fac_right, sq.fac_left⟩⟩

def pathExtension : PathExtension f Q := (pathExtension_nonempty f Q hf).some

namespace PathExtension
variable {f Q} (w : PathExtension f Q)

def target : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X := w.family ≫ equivalencePathEndpoint X 1

omit [Quasicategory X] in
lemma target_boundary : boundaryι ≫ w.target =
    (f.postcomp (equivalencePathEndpoint X 1)).diagram := by
  rw [target, ← Category.assoc, w.boundary, diagram_postcomp]

def comparison : FunctorIso Q w.target :=
  (eqToIso (congrArg (fun g => HomotopyCategory.mk (functorVertex g)) w.source)).symm ≪≫
    equivalencePathFamilyIso w.family

lemma target_isPullback (hQ : IsPullbackSquare Q) : IsPullbackSquare w.target :=
  IsPullbackSquare.of_functorIso hQ w.comparison

end PathExtension
end SerrePositivity.KST.LocalizingInvariants.SquareFrame
