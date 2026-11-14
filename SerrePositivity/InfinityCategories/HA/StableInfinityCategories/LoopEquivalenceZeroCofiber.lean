module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopEquivalenceCofiberRotation
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionEquivalenceOfLoopEquivalence
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberRotationComparison

/-!
概要：実 loop 同値から、零 cofiber を持つ辺の可逆性を検出する。
方針：一回の回転の外側と右面を懸垂図式として比較し、終点評価で反映する。
規約：一般安定性と有限余極限を仮定しない。
使われ方：一般零角の fiber/cofiber 判定の比較辺の可逆性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：零 cofiber を持つ実四角形の底辺は可逆である。
方針：同じ終点を持つ二つの懸垂図式の比較射を評価する。
規約：辺とその指定 cofiber 四角形を保持する。
使われ方：一般零角の比較の可逆性の判定。 -/
lemma ZeroTriangle.isIso_bottom_of_zero_cofiber_of_loopEquivalence {X : SSet.{u}}
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex X] [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits X]
    (s : X ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X) (hs : s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0))
    (t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsCofiberSequence t)
    (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex t.square 1 1)) : IsIso (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoBottom t.square) := by
  obtain ⟨r⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.nonempty_cofiberRotationRectangle_of_loopEquivalence s hs hΩ t ht
  let b : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare r.diagram 0) 0 0) := {
    square := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare r.diagram 0
    zero_corner := by
      change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare r.diagram 2) 1 1)
      rw [r.left_eq]
      exact hz
    source_eq := rfl
    other_zero := r.zero_end
    isPushout := r.right_isPushout }
  let ι := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X)
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsSuspensionDiagramVertex).ι
  let H := (hoFunctor.map ι).toFunctor
  let hH := (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι
    ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X)
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsSuspensionDiagramVertex (X := X))).toHoFullyFaithful
  let a : (HomotopyCategory.mk r.suspensionSquare.diagramVertex :
      hoFunctor.obj (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagrams X)) ⟶ HomotopyCategory.mk b.diagramVertex :=
    hH.preimage (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterToRightHom r.diagram)
  have ha : H.map a = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterToRightHom r.diagram := hH.map_preimage _
  let E := (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagramEvaluation X 1 1)).toFunctor
  have hE := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionDiagramEvaluation_target_isQCatEquivalence_of_loopEquivalence
    s hs hΩ).isFullyFaithful.toHoFullyFaithful
  have htarget : IsIso ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X 1 1).map
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterToRightHom r.diagram)) := by
    change IsIso (Arrow.mk ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X 1 1).map
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterToRightHom r.diagram))).hom
    rw [congrArg Arrow.mk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterToRightHom_target r.diagram)]
    change IsIso (𝟙 (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare r.diagram 1) 1 1))
    exact ⟨⟨𝟙 _, Category.id_comp _, Category.id_comp _⟩⟩
  have hi : IsIso (E.map a) := by
    have he := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoMap_comp ι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (𝟙 (Δ[1] ⊗ Δ[1] : SSet.{u})) 1 1)) a
    change (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X 1 1).map (H.map a) = E.map a at he
    change IsIso (Arrow.mk (E.map a)).hom
    rw [← congrArg Arrow.mk he, ha]
    exact htarget
  have : IsIso a := hE.isIso_of_isIso_map a
  have hi₀ : IsIso ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X 0 0).map
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterToRightHom r.diagram)) := by
    rw [← ha]
    infer_instance
  have he := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterToRightHom_source_arrow r.diagram
  rw [r.left_eq] at he
  change IsIso (Arrow.mk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoBottom t.square)).hom
  rw [← he]
  exact hi₀

with_weak_namespace _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle export _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroTriangle (isIso_bottom_of_zero_cofiber_of_loopEquivalence)


end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
