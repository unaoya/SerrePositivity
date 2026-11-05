module

public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCoreSliceCones
public import SerrePositivity.KST.LocalizingInvariants.VerdierCoreQuotientCofinality

/-!
概要：有限商錐の全 slice 同型付き回収から、元の core 逆像射影の cofinality を導く。
方針：任意の終対象付き右ファイブレーションの引き戻し内で有限錐を構成する。
規約：元の射影を扱い、本質的全射性だけから充満忠実性を推論しない。
使われ方：c5 の全標準単体の関手圏での有限商錐回収を消費する。
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

lemma exists_corePullback_finiteCone_of_quotientConeRecovery
    {X Z : SSet.{u}} [Quasicategory X] [Quasicategory Z] (q : X ⟶ Z)
    (h : ∀ (K : SSet.{u}) [K.Finite] (p : K ⟶ X) (t : JoinCone (p ≫ q)),
      ∃ c : JoinCone p, Nonempty (VertexIso (X := sliceOver (p ≫ q))
        (mapJoinCone q c) t))
    {Y : SSet.{u}} [Quasicategory Y] (r : Y ⟶ (quasicategoryCore Z : SSet.{u}))
    [RightFibration r] {y : Y _⦋0⦌} (hy : IsTerminalVertex y)
    {K : SSet.{u}} [K.Finite]
    (a : K ⟶ pullback ((quasicategoryCore Z).fromPreimage q) r) : Nonempty (JoinCone a) := by
  let W := ((quasicategoryCore Z).preimage q : SSet.{u})
  let Q := (quasicategoryCore Z).fromPreimage q
  let : Quasicategory W := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.corePreimage_quasicategory q
  let coreι := (quasicategoryCore Z).ι
  let P := (a ≫ pullback.fst Q r) ≫ ((quasicategoryCore Z).preimage q).ι
  let γ := a ≫ pullback.snd Q r
  let R := r ≫ coreι
  have hγ : P ≫ q = γ ≫ R := by
    change ((a ≫ pullback.fst Q r) ≫ ((quasicategoryCore Z).preimage q).ι) ≫ q = _
    change ((a ≫ pullback.fst Q r) ≫ Q) ≫ coreι = _
    have he : pullback.fst Q r ≫ Q = pullback.snd Q r ≫ r := pullback.condition
    simpa only [γ, R, Category.assoc] using congrArg (fun k => a ≫ k ≫ coreι) he
  have hY := rightFibration_isContractibleKan_of_terminal r hy
  obtain ⟨G, hG⟩ := (hY.isInitialVertex y).exists_cosliceLift γ
  let cY : JoinCone γ := ⟨sliceUnderUncurry G, (sliceUnderUncurry_projection G).trans hG⟩
  let t : JoinCone (P ≫ q) := ⟨cY.val ≫ R, by
    rw [← Category.assoc, cY.property]
    exact hγ.symm⟩
  obtain ⟨c, ⟨e⟩⟩ := h K P t
  have hInv : InvertsEdges (c.val ≫ q) Set.univ := by
    have hcIso := coneFunctorIsoOfVertexIso (mapJoinCone q c) t e
    exact (invertsEdges_functorIso_iff hcIso Set.univ).mpr
      ((_root_.SerrePositivity.InfinityCategories.Derived.Localization.invertsAllEdges_toKan (cY.val ≫ r)).comp coreι)
  let cWval := corePreimageLift q c.val hInv
  have hcW : joinInr (Δ[0] : SSet.{u}) K ≫ cWval = a ≫ pullback.fst Q r := by
    apply (cancel_mono ((quasicategoryCore Z).preimage q).ι).mp
    rw [Category.assoc, corePreimageLift_ι, c.property]
  let cW : JoinCone (a ≫ pullback.fst Q r) := ⟨cWval, hcW⟩
  let cQ : JoinCone (γ ≫ R) := ⟨c.val ≫ q, by
    rw [← Category.assoc, c.property, hγ]⟩
  obtain ⟨v, hv⟩ := homotopyCategory_homMk_surjective
    (X := sliceOver (P ≫ q)) (mapJoinCone q c) t e.hom
  have hvInv : IsInvertibleEdge (X := sliceOver (P ≫ q)) v := by
    change IsIso (Truncated.HomotopyCategory.homMk v)
    rw [hv]
    infer_instance
  obtain ⟨v', hv'⟩ := exists_coneEdge_rebase_of_val_eq v
    (show (mapJoinCone q c).val = cQ.val from rfl)
    (show t.val = (mapJoinCone R cY).val from rfl)
  have hv'Inv : IsIso (Truncated.HomotopyCategory.homMk v') := by
    apply derived_rightFibration_reflects_invertibleEdge (sliceOverProjection (γ ≫ R)) v'
    exact (isInvertibleEdge_congr hv').mpr
      (hvInv.map (sliceOverProjection (P ≫ q)))
  have hr : F1B.EquivalenceLifting r := F2.Presentable.rightFibration_equivalenceLifting r
  have hι : F1B.EquivalenceLifting coreι := coreInclusion_equivalenceLifting Z
  have hR : F1B.EquivalenceLifting R := by
    intro U V j hm he
    have := hr j hm he
    have := hι j hm he
    infer_instance
  have hs : F1B.EquivalenceLifting (sliceOverPostcomp γ R) :=
    F2.Presentable.sliceOverPostcomp_equivalenceLifting γ R hR
  obtain ⟨dY, hdY, _⟩ := F1B.exists_kanVertexIso_lift_target
    (sliceOverPostcomp γ R) hs cY cQ (asIso (Truncated.HomotopyCategory.homMk v'))
  have hdYval : dY.val ≫ R = c.val ≫ q := congrArg Subtype.val hdY
  have hpair : cW.val ≫ Q = dY.val ≫ r := by
    apply (cancel_mono coreι).mp
    change (cWval ≫ Q) ≫ coreι = (dY.val ≫ r) ≫ coreι
    change (cWval ≫ ((quasicategoryCore Z).preimage q).ι) ≫ q = _
    rw [corePreimageLift_ι]
    exact hdYval.symm
  let F := pullback.lift cW.val dY.val hpair
  refine ⟨⟨F, ?_⟩⟩
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst]
    exact cW.property
  · rw [Category.assoc, pullback.lift_snd]
    exact dY.property


/-- 全有限商錐の同じ slice 比較付き回収は、元の core 逆像射影の left cofinality を与える。 -/
lemma corePreimageProjection_isLeftCofinal_of_quotientConeRecovery
    {X Z : SSet.{u}} [Quasicategory X] [Quasicategory Z] (q : X ⟶ Z)
    (h : ∀ (K : SSet.{u}) [K.Finite] (p : K ⟶ X) (t : JoinCone (p ≫ q)),
      ∃ c : JoinCone p, Nonempty (VertexIso (X := sliceOver (p ≫ q))
        (mapJoinCone q c) t)) :
    IsLeftCofinal ((quasicategoryCore Z).fromPreimage q) := by
  let W := ((quasicategoryCore Z).preimage q : SSet.{u})
  let Q := (quasicategoryCore Z).fromPreimage q
  let : Quasicategory W := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.corePreimage_quasicategory q
  apply isLeftCofinal_of_weaklyContractible_slices Q
  intro c
  let r := sliceOverProjection (SSet.yonedaEquiv.symm c)
  let T := pullback Q r
  have hcones : ∀ {K : SSet.{u}} [K.Finite] (a : K ⟶ T), Nonempty (JoinCone a) := by
    intro K _ a
    exact exists_corePullback_finiteCone_of_quotientConeRecovery q h r
      (F1B.sliceIdentityCone_isTerminalVertex c) a
  have : F2.IsFilteredInfinity T.op := isFilteredInfinity_op_of_finiteCones T hcones
  exact isWeaklyContractible_of_op (F2.isWeaklyContractible_of_isFilteredInfinity T.op)

end SerrePositivity.KST.LocalizingInvariants
