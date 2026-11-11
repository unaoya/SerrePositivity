module

public import SerrePositivity.KST.Spectra.PointedHomotopyGroupDiagram
public import Mathlib.CategoryTheory.Action.Basic

/-!
概要：点つき Kan 複体の群作用が正次数ホモトピー群に誘導する群作用。
方針：一対象群圏の図式へ移し、ホモトピー群の図式を再び作用の圏へ戻す。
規約：k は実際の次数 k+1。非可換な π_1 も許す。
使われ方：Goerss–Jardine I §7、VIII §2。群 cochain の π_* の係数の作用。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.PointedActionCochains

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：点つき作用の正次数ホモトピー群に誘導される群の圏の作用。
方針：群圏の図式へホモトピー群を適用し、作用と図式の同値で戻す。
規約：係数の基礎単体集合は Kan とする。
使われ方：Goerss–Jardine VIII §2。非斉次 cochain の群の係数。 -/
def homotopyAction {G : Type u} [Group G] (B : Action PointedSimplicialSet.{u} G)
    [KanComplex B.V.right] (k : ℕ) : Action GrpCat.{u} G := by
  let D := Action.FunctorCategoryEquivalence.functor.obj B
  let : ∀ j, KanComplex (D.obj j).right :=
    fun _ ↦ inferInstanceAs (KanComplex B.V.right)
  exact Action.FunctorCategoryEquivalence.inverse.obj (KanHomotopyGroup.diagram D k)

lemma homotopyAction_ρ_apply {G : Type u} [Group G]
    (B : Action PointedSimplicialSet.{u} G) [KanComplex B.V.right] (k : ℕ) (g : G)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup B.V.right k B.V.basepoint) :
    ((homotopyAction B k).ρ g).asHom a =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (B.ρ g).asHom.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint _) a := rfl

end

end SerrePositivity.KST.Spectra.PointedActionCochains
