module

public import SerrePositivity.KST.LocalizingInvariants.FiberConeHomotopyUniqueness
public import SerrePositivity.InfinityCategories.Core.HomotopyPrecomposition

/-!
概要：pullback 四角形間の比較の類を、元の cospan の比較から一意に決定する。
方針：正方形を普遍錐へ移し、図式射影の忠実性で比較して元の形状へ戻す。
規約：四辺の h の可換式には弱めない。使われ方：fiber 模型の全 cube との照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.FiberSquareHomotopy

lemma restriction {X : SSet.{u}}
    {F G : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X} (H : SSet.Homotopy F G) :
    (hoFunctor.map (coneRestriction (horn 2 2 : SSet.{u}) X)).toFunctor.map
      (SSet.Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy (stableHomotopyPrecomp cospanConeSquareIso.hom H))) =
    SSet.Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy (stableHomotopyPrecomp cospanSquareBoundary H)) := by
  change (hoFunctor.map ((pre (joinInr Δ[0] (horn 2 2 : SSet.{u}))).app X)).toFunctor.map
    (SSet.Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy (stableHomotopyPrecomp cospanConeSquareIso.hom H))) = _
  rw [homMk_functorEdge_precomp]
  congr 1

lemma homMk_eq_of_cospan {X : SSet.{u}} [Quasicategory X]
    (F G : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X)
    (hF : IsPullbackSquare F) (hG : IsPullbackSquare G)
    (H J : SSet.Homotopy F G)
    (h : Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (stableHomotopyPrecomp cospanSquareBoundary H)) =
      Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (stableHomotopyPrecomp cospanSquareBoundary J))) :
    Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H) =
      Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy J) := by
  have hc := FiberCone.homotopy_homMk_eq (pullbackCone F) (pullbackCone G) hF hG
    (stableHomotopyPrecomp cospanConeSquareIso.hom H)
    (stableHomotopyPrecomp cospanConeSquareIso.hom J)
    ((restriction H).trans (h.trans (restriction J).symm))
  have he := congrArg (fun f ↦
    (hoFunctor.map ((pre cospanConeSquareIso.inv).app X)).toFunctor.map f) hc
  rw [homMk_functorEdge_precomp, homMk_functorEdge_precomp] at he
  apply Arrow.mk_injective
  exact (homMk_functorEdge_precomp_inv_hom_arrow cospanConeSquareIso H).symm.trans
    ((congrArg Arrow.mk he).trans
      (homMk_functorEdge_precomp_inv_hom_arrow cospanConeSquareIso J))

end SerrePositivity.KST.LocalizingInvariants.FiberSquareHomotopy
