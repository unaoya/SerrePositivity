module
public import SerrePositivity.InfinityCategories.Stable.LoopEquivalenceCofiberRotation
public import SerrePositivity.InfinityCategories.Stable.SuspensionEquivalenceOfLoopEquivalence
public import SerrePositivity.InfinityCategories.Stable.CofiberRotationComparison

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
namespace SerrePositivity.InfinityCategories

/-- 概要：零 cofiber を持つ実四角形の底辺は可逆である。
方針：同じ終点を持つ二つの懸垂図式の比較射を評価する。
規約：辺とその指定 cofiber 四角形を保持する。
使われ方：一般零角の比較の可逆性の判定。 -/
lemma ZeroTriangle.isIso_bottom_of_zero_cofiber_of_loopEquivalence {X : SSet.{u}}
    [Quasicategory X] [HasZeroVertex X] [HasFiniteLimits X]
    (s : X ⟶ loopDiagrams X) (hs : s ≫ loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : IsQCatEquivalence (s ≫ loopDiagramEvaluation X 0 0))
    (t : ZeroTriangle X) (ht : IsCofiberSequence t)
    (hz : IsZeroVertex (squareVertex t.square 1 1)) : IsIso (squareHoBottom t.square) := by
  obtain ⟨r⟩ := nonempty_cofiberRotationRectangle_of_loopEquivalence s hs hΩ t ht
  let b : SuspensionSquare (squareVertex (pastingSquare r.diagram 0) 0 0) := {
    square := pastingSquare r.diagram 0
    zero_corner := by
      change IsZeroVertex (squareVertex (pastingSquare r.diagram 2) 1 1)
      rw [r.left_eq]
      exact hz
    source_eq := rfl
    other_zero := r.zero_end
    isPushout := r.right_isPushout }
  let ι := (fullSubcomplexOnVertices ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X)
    IsSuspensionDiagramVertex).ι
  let H := (hoFunctor.map ι).toFunctor
  let hH := (isFullyFaithful_fullSubcomplexOnVertices_ι
    ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X)
    (IsSuspensionDiagramVertex (X := X))).toHoFullyFaithful
  let a : (HomotopyCategory.mk r.suspensionSquare.diagramVertex :
      hoFunctor.obj (suspensionDiagrams X)) ⟶ HomotopyCategory.mk b.diagramVertex :=
    hH.preimage (pastingOuterToRightHom r.diagram)
  have ha : H.map a = pastingOuterToRightHom r.diagram := hH.map_preimage _
  let E := (hoFunctor.map (suspensionDiagramEvaluation X 1 1)).toFunctor
  have hE := (suspensionDiagramEvaluation_target_isQCatEquivalence_of_loopEquivalence
    s hs hΩ).isFullyFaithful.toHoFullyFaithful
  have htarget : IsIso ((squareDiagramHoEvaluation X 1 1).map
      (pastingOuterToRightHom r.diagram)) := by
    change IsIso (Arrow.mk ((squareDiagramHoEvaluation X 1 1).map
      (pastingOuterToRightHom r.diagram))).hom
    rw [congrArg Arrow.mk (pastingOuterToRightHom_target r.diagram)]
    change IsIso (𝟙 (squareHoVertex (pastingSquare r.diagram 1) 1 1))
    exact ⟨⟨𝟙 _, Category.id_comp _, Category.id_comp _⟩⟩
  have hi : IsIso (E.map a) := by
    have he := stableHoMap_comp ι (evaluateFunctorAt
      (squareVertex (𝟙 (Δ[1] ⊗ Δ[1] : SSet.{u})) 1 1)) a
    change (squareDiagramHoEvaluation X 1 1).map (H.map a) = E.map a at he
    change IsIso (Arrow.mk (E.map a)).hom
    rw [← congrArg Arrow.mk he, ha]
    exact htarget
  have : IsIso a := hE.isIso_of_isIso_map a
  have hi₀ : IsIso ((squareDiagramHoEvaluation X 0 0).map
      (pastingOuterToRightHom r.diagram)) := by
    rw [← ha]
    infer_instance
  have he := pastingOuterToRightHom_source_arrow r.diagram
  rw [r.left_eq] at he
  change IsIso (Arrow.mk (squareHoBottom t.square)).hom
  rw [← he]
  exact hi₀

end SerrePositivity.InfinityCategories
