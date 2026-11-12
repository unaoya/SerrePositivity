module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CompactFactorization
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.ConeAnodyne
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CoslicePostcompTransport
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.RightFibrationEdgeTarget

/-!
概要：compact な像を持つ始対象から、left fibration 内の指定点へ実因子化を作る。
方針：点下の後合成の公開 trivial Kan 性で、compact 源の実因子化を全空間へ戻す。
規約：指定した余錐脚と同じ底辺を被覆する全空間の実辺を結論する。
使われ方：HTT 5.5.4.13 の小さい全余錐の因子化の準備。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories


/-- compact な始対象像を持つ left fibration の指定点は、同じ余錐脚の上で一段へ因子化する。 -/
lemma compactInitial_leftFibration_factorization {κ : Cardinal.{u}}
    {E C : SSet.{u + 1}} [Quasicategory C] (p : E ⟶ C) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
    (e : E _⦋0⦌) (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex e)
    (hcompact : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} κ (p.app _ e))
    {K : SSet.{u}} [Quasicategory K] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ K]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ C)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) (t : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p c.vertex) _⦋0⦌) :
    ∃ j : K _⦋0⦌, ∃ w : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (D.app _ (ULift.up j))) _⦋0⦌,
      ∃ k : E.Edge w.val t.val, (k.map p).edge = (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeTransportLeg c (ULift.up j)).edge := by
  obtain ⟨e0⟩ := he.nonempty_edge t.val
  let u := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.edgeCosliceVertex e0
  let a := SSet.yonedaEquiv.symm e
  let b := SSet.yonedaEquiv.symm (p.app _ e)
  have hab : a ≫ p = b := SSet.yonedaEquiv_symm_comp e p
  let q := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableCoslicePostcomp a p b hab
  have hq : q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection b = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a ≫ p :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableCoslicePostcomp_projection a p b hab
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration q := by
    have hq0 := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.ConeAnodyne.sliceUnderPostcomp_trivialKanFibration a p
    exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations.comp_mem _ _ hq0.mem
      (MorphismProperty.of_isIso _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations _)⟩
  let tB : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection b) c.vertex) _⦋0⦌ :=
    ⟨q.app _ u, by
      have hu := ConcreteCategory.congr_hom (NatTrans.congr_app hq (Opposite.op ⦋0⦌)) u
      change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection b).app _ (q.app _ u) = _
      change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection b).app _ (q.app _ u) =
        p.app _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a).app _ u) at hu
      rw [hu]
      change p.app _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.edgeCosliceVertex e0)) = _
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.edgeCosliceVertex_projection]
      exact t.property⟩
  obtain ⟨j, wB, kB, hkB⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.compactSource_coslice_factorization hcompact D c hc tB
  obtain ⟨F, hF, hFq⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.rightFibration_liftEdge_target q u kB.toTruncated
  let kEdge := SSet.yonedaEquiv (F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a)
  let wE := E.δ 1 kEdge
  have htarget : E.δ 0 kEdge = t.val := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, ← Category.assoc, hF,
      SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.edgeCosliceVertex_projection e0
  let kE : Truncated.Edge (X := (truncation 2).obj E) wE t.val := ⟨kEdge, rfl, htarget⟩
  have hmap : (kE.map ((truncation 2).map p)).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeTransportLeg c (ULift.up j)).edge := by
    change p.app _ (SSet.yonedaEquiv (F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a)) = _
    rw [← SSet.yonedaEquiv_comp]
    have hcomp : (F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a) ≫ p =
        SSet.yonedaEquiv.symm kB.edge ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection b := by
      rw [Category.assoc, ← hq, ← Category.assoc, hFq]
      rfl
    rw [hcomp, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    exact hkB
  have hw : p.app _ wE = D.app _ (ULift.up j) := by
    have hs := (kE.map ((truncation 2).map p)).src_eq
    change C.δ 1 (kE.map ((truncation 2).map p)).edge = p.app _ wE at hs
    rw [← hs, hmap]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeTransportLeg c (ULift.up j)).src_eq
  let w : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (D.app _ (ULift.up j))) _⦋0⦌ :=
    ⟨wE, hw.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero _).symm⟩
  exact ⟨j, w, SSet.Edge.ofTruncated kE, hmap⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
