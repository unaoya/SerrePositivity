module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.CompactFactorization
public import SerrePositivity.InfinityCategories.Core.InitialHomotopy
public import SerrePositivity.InfinityCategories.Core.ConeAnodyne
public import SerrePositivity.InfinityCategories.F1.CoslicePostcompTransport
public import SerrePositivity.InfinityCategories.Stable.RightFibrationEdgeTarget

/-!
概要：compact な像を持つ始対象から、left fibration 内の指定点へ実因子化を作る。
方針：点下の後合成の公開 trivial Kan 性で、compact 源の実因子化を全空間へ戻す。
規約：指定した余錐脚と同じ底辺を被覆する全空間の実辺を結論する。
使われ方：HTT 5.5.4.13 の小さい全余錐の因子化の準備。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits Compact

/-- compact な始対象像を持つ left fibration の指定点は、同じ余錐脚の上で一段へ因子化する。 -/
lemma compactInitial_leftFibration_factorization {κ : Cardinal.{u}}
    {E C : SSet.{u + 1}} [Quasicategory C] (p : E ⟶ C) [LeftFibration p]
    (e : E _⦋0⦌) (he : IsInitialVertex e)
    (hcompact : Compact.IsKappaCompact.{u, u + 1} κ (p.app _ e))
    {K : SSet.{u}} [Quasicategory K] [IsKappaFiltered κ K]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ C)
    (c : JoinCocone D) (hc : IsColimitCone c) (t : (vertexFiber p c.vertex) _⦋0⦌) :
    ∃ j : K _⦋0⦌, ∃ w : (vertexFiber p (D.app _ (ULift.up j))) _⦋0⦌,
      ∃ k : E.Edge w.val t.val, (k.map p).edge = (coconeTransportLeg c (ULift.up j)).edge := by
  obtain ⟨e0⟩ := he.nonempty_edge t.val
  let u := edgeCosliceVertex e0
  let a := SSet.yonedaEquiv.symm e
  let b := SSet.yonedaEquiv.symm (p.app _ e)
  have hab : a ≫ p = b := SSet.yonedaEquiv_symm_comp e p
  let q := stableCoslicePostcomp a p b hab
  have hq : q ≫ sliceUnderProjection b = sliceUnderProjection a ≫ p :=
    stableCoslicePostcomp_projection a p b hab
  have : TrivialKanFibration q := by
    have hq0 := sliceUnderPostcomp_trivialKanFibration a p
    exact ⟨trivialKanFibrations.comp_mem _ _ hq0.mem
      (MorphismProperty.of_isIso trivialKanFibrations _)⟩
  let tB : (vertexFiber (sliceUnderProjection b) c.vertex) _⦋0⦌ :=
    ⟨q.app _ u, by
      have hu := ConcreteCategory.congr_hom (NatTrans.congr_app hq (Opposite.op ⦋0⦌)) u
      change (sliceUnderProjection b).app _ (q.app _ u) = _
      change (sliceUnderProjection b).app _ (q.app _ u) =
        p.app _ ((sliceUnderProjection a).app _ u) at hu
      rw [hu]
      change p.app _ ((sliceUnderProjection a).app _ (edgeCosliceVertex e0)) = _
      rw [edgeCosliceVertex_projection]
      exact t.property⟩
  obtain ⟨j, wB, kB, hkB⟩ := compactSource_coslice_factorization hcompact D c hc tB
  obtain ⟨F, hF, hFq⟩ := rightFibration_liftEdge_target q u kB.toTruncated
  let kEdge := SSet.yonedaEquiv (F ≫ sliceUnderProjection a)
  let wE := E.δ 1 kEdge
  have htarget : E.δ 0 kEdge = t.val := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, ← Category.assoc, hF,
      SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    exact edgeCosliceVertex_projection e0
  let kE : Truncated.Edge (X := (truncation 2).obj E) wE t.val := ⟨kEdge, rfl, htarget⟩
  have hmap : (kE.map ((truncation 2).map p)).edge =
      (coconeTransportLeg c (ULift.up j)).edge := by
    change p.app _ (SSet.yonedaEquiv (F ≫ sliceUnderProjection a)) = _
    rw [← SSet.yonedaEquiv_comp]
    have hcomp : (F ≫ sliceUnderProjection a) ≫ p =
        SSet.yonedaEquiv.symm kB.edge ≫ sliceUnderProjection b := by
      rw [Category.assoc, ← hq, ← Category.assoc, hFq]
      rfl
    rw [hcomp, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    exact hkB
  have hw : p.app _ wE = D.app _ (ULift.up j) := by
    have hs := (kE.map ((truncation 2).map p)).src_eq
    change C.δ 1 (kE.map ((truncation 2).map p)).edge = p.app _ wE at hs
    rw [← hs, hmap]
    exact (coconeTransportLeg c (ULift.up j)).src_eq
  let w : (vertexFiber p (D.app _ (ULift.up j))) _⦋0⦌ :=
    ⟨wE, hw.trans (pinchedConstant_zero _).symm⟩
  exact ⟨j, w, SSet.Edge.ofTruncated kE, hmap⟩

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
