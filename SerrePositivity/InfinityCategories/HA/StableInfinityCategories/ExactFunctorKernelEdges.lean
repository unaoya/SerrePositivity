module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberLocalizingEdges
/-!
概要：完全関手の零対象核に cofiber を持つ辺は、同じ関手が反転する辺と一致する。
方針：実 cofiber 四角形の可逆性と零性の同値を両向きに使う。
規約：元の辺・実 cofiber を保持し、局所化や核の存在を仮定しない。
使われ方：D-16 の thick 核の辺集合を実商の反転飽和へ同定する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open CategoryTheory SSet
open scoped _root_.Simplicial
variable {X Y : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
  [Quasicategory Y] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable Y] (F : X ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor F]

lemma cofiberLocalizingEdges_zeroKernel_eq_invertedEdges :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges {x | _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (F.app (Opposite.op ⦋0⦌) x)} =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertedEdges F := by
  apply Set.Subset.antisymm
  · exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.inverts_cofiberLocalizingEdges_of_kills F _ (fun _ h => h)
  · intro a ha
    let s := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenCofiberSquare (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex a)
    exact ⟨s, s.cofiber, (s.map_isInvertible_iff_zero F).1 ha, ⟨Iso.refl _⟩⟩

lemma cofiberLocalizingEdges_eq_invertedEdges_of_kernel
    (P : Set (X _⦋0⦌))
    (hP : ∀ x, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (F.app (Opposite.op ⦋0⦌) x) ↔ x ∈ P) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges P = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertedEdges F := by
  have h : P = {x | _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (F.app (Opposite.op ⦋0⦌) x)} :=
    Set.ext (fun x => (hP x).symm)
  rw [h]
  exact cofiberLocalizingEdges_zeroKernel_eq_invertedEdges F

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
