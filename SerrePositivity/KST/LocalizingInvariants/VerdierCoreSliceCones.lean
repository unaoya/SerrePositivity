module

public import SerrePositivity.KST.LocalizingInvariants.VerdierQuotientConeRefinement
public import SerrePositivity.KST.LocalizingInvariants.RightFibrationConeTransport
public import SerrePositivity.KST.LocalizingInvariants.CoreInclusionEquivalenceLifting
public import SerrePositivity.KST.LocalizingInvariants.CorePreimageComparisonPrism
public import SerrePositivity.KST.Fibration.RelativeDiagram
public import SerrePositivity.InfinityCategories.F2.Presentable.RightFibrationEquivalenceLifting
public import SerrePositivity.InfinityCategories.F2.Presentable.SlicePostcompEquivalenceLifting
public import SerrePositivity.InfinityCategories.F1B.Fibrations.VertexIsoLifting
public import SerrePositivity.InfinityCategories.Core.LeftFibrationTerminalFiber
public import SerrePositivity.InfinityCategories.Stable.ConeEdgeRebase
public import SerrePositivity.InfinityCategories.Core.InnerPullback

/-!
概要：元の core 逆像射影の slice 内で、任意の有限図式の実錐を構成する。
方針：終対象付き右ファイブレーションの錐を商錐回収へ渡し、同じ全比較で slice へ戻す。
規約：完成側の境界持ち上げや零次比較の充満忠実性を追加入力にしない。
使われ方：c5 の零次比較の Quillen A 判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants

lemma corePreimage_quasicategory {B C : SSet.{u}} [Quasicategory B] (q : B ⟶ C) :
    Quasicategory ((quasicategoryCore C).preimage q : SSet.{u}) := by
  have he : relativeDiagram q (fun _ : Unit => 𝟙 B) = (quasicategoryCore C).preimage q := by
    ext n s
    change (∀ _ : Unit, (𝟙 B ≫ q).app n s ∈ (quasicategoryCore C).obj n) ↔
      q.app n s ∈ (quasicategoryCore C).obj n
    simp only [Category.id_comp, forall_const]
  rw [← he]
  infer_instance

variable {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}

local notation "W" => (Subcomplex.preimage (quasicategoryCore C.obj) q.hom : SSet)
local notation "Q" => Subcomplex.fromPreimage (quasicategoryCore C.obj) q.hom

/-- 終対象付き右ファイブレーションへの同じ引き戻し内で、任意の有限図式に実錐がある。 -/
lemma exists_verdierCorePullback_finiteCone (h : IsVerdierSequence i q)
    {Y : SSet.{u}} [Quasicategory Y] (r : Y ⟶ (quasicategoryCore C.obj : SSet.{u}))
    [RightFibration r] {y : Y _⦋0⦌} (hy : IsTerminalVertex y)
    {K : SSet.{u}} [K.Finite] (a : K ⟶ pullback Q r) : Nonempty (JoinCone a) := by
  let : Quasicategory W := corePreimage_quasicategory q.hom
  let coreι := (quasicategoryCore C.obj).ι
  let P := (a ≫ pullback.fst Q r) ≫ ((quasicategoryCore C.obj).preimage q.hom).ι
  let γ := a ≫ pullback.snd Q r
  let R := r ≫ coreι
  have hγ : P ≫ q.hom = γ ≫ R := by
    change ((a ≫ pullback.fst Q r) ≫ ((quasicategoryCore C.obj).preimage q.hom).ι) ≫ q.hom = _
    change ((a ≫ pullback.fst Q r) ≫ Q) ≫ coreι = _
    have he : pullback.fst Q r ≫ Q = pullback.snd Q r ≫ r := pullback.condition
    simpa only [γ, R, Category.assoc] using congrArg (fun k => a ≫ k ≫ coreι) he
  have hY := rightFibration_isContractibleKan_of_terminal r hy
  obtain ⟨G, hG⟩ := (hY.isInitialVertex y).exists_cosliceLift γ
  let cY : JoinCone γ := ⟨sliceUnderUncurry G, (sliceUnderUncurry_projection G).trans hG⟩
  let t : JoinCone (P ≫ q.hom) := ⟨cY.val ≫ R, by
    rw [← Category.assoc, cY.property]
    exact hγ.symm⟩
  obtain ⟨c, ⟨e⟩⟩ := exists_verdierQuotientConeIsoRefinement h P t
  have hInv : InvertsEdges (c.val ≫ q.hom) Set.univ := by
    have hcIso := coneFunctorIsoOfVertexIso (mapJoinCone q.hom c) t e
    exact (invertsEdges_functorIso_iff hcIso Set.univ).mpr
      ((invertsAllEdges_toKan (cY.val ≫ r)).comp coreι)
  let cWval := corePreimageLift q.hom c.val hInv
  have hcW : joinInr (Δ[0] : SSet.{u}) K ≫ cWval = a ≫ pullback.fst Q r := by
    apply (cancel_mono ((quasicategoryCore C.obj).preimage q.hom).ι).mp
    rw [Category.assoc, corePreimageLift_ι, c.property]
  let cW : JoinCone (a ≫ pullback.fst Q r) := ⟨cWval, hcW⟩
  let cQ : JoinCone (γ ≫ R) := ⟨c.val ≫ q.hom, by
    rw [← Category.assoc, c.property, hγ]⟩
  obtain ⟨v, hv⟩ := homotopyCategory_homMk_surjective
    (X := sliceOver (P ≫ q.hom)) (mapJoinCone q.hom c) t e.hom
  have hvInv : IsInvertibleEdge (X := sliceOver (P ≫ q.hom)) v := by
    change IsIso (Truncated.HomotopyCategory.homMk v)
    rw [hv]
    infer_instance
  obtain ⟨v', hv'⟩ := exists_coneEdge_rebase_of_val_eq v
    (show (mapJoinCone q.hom c).val = cQ.val from rfl)
    (show t.val = (mapJoinCone R cY).val from rfl)
  have hv'Inv : IsIso (Truncated.HomotopyCategory.homMk v') := by
    apply derived_rightFibration_reflects_invertibleEdge (sliceOverProjection (γ ≫ R)) v'
    exact (isInvertibleEdge_congr hv').mpr
      (hvInv.map (sliceOverProjection (P ≫ q.hom)))
  have hr : F1B.EquivalenceLifting r := F2.Presentable.rightFibration_equivalenceLifting r
  have hι : F1B.EquivalenceLifting coreι := coreInclusion_equivalenceLifting C.obj
  have hR : F1B.EquivalenceLifting R := by
    intro U V j hm he
    have := hr j hm he
    have := hι j hm he
    infer_instance
  have hs : F1B.EquivalenceLifting (sliceOverPostcomp γ R) :=
    F2.Presentable.sliceOverPostcomp_equivalenceLifting γ R hR
  obtain ⟨dY, hdY, _⟩ := F1B.exists_kanVertexIso_lift_target
    (sliceOverPostcomp γ R) hs cY cQ (asIso (Truncated.HomotopyCategory.homMk v'))
  have hdYval : dY.val ≫ R = c.val ≫ q.hom := congrArg Subtype.val hdY
  have hpair : cW.val ≫ Q = dY.val ≫ r := by
    apply (cancel_mono coreι).mp
    change (cWval ≫ Q) ≫ coreι = (dY.val ≫ r) ≫ coreι
    change (cWval ≫ ((quasicategoryCore C.obj).preimage q.hom).ι) ≫ q.hom = _
    rw [corePreimageLift_ι]
    exact hdYval.symm
  let F := pullback.lift cW.val dY.val hpair
  refine ⟨⟨F, ?_⟩⟩
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst]
    exact cW.property
  · rw [Category.assoc, pullback.lift_snd]
    exact dY.property

end SerrePositivity.KST.LocalizingInvariants
