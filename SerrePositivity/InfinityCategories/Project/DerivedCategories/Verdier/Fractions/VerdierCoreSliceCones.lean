module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierQuotientConeRefinement
public import SerrePositivity.KST.LocalizingInvariants.RightFibrationConeTransport
public import SerrePositivity.KST.LocalizingInvariants.CoreInclusionEquivalenceLifting
public import SerrePositivity.KST.LocalizingInvariants.CorePreimageComparisonPrism
public import SerrePositivity.KST.Fibration.RelativeDiagram
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.RightFibrationEquivalenceLifting
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.SlicePostcompEquivalenceLifting
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.VertexIsoLifting
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.LeftFibrationTerminalFiber
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ConeEdgeRebase
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.InnerPullback

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
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions
open _root_.SerrePositivity.KST.LocalizingInvariants

lemma corePreimage_quasicategory {B C : SSet.{u}} [Quasicategory B] (q : B ⟶ C) :
    Quasicategory ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C).preimage q : SSet.{u}) := by
  have he : relativeDiagram q (fun _ : Unit => 𝟙 B) = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C).preimage q := by
    ext n s
    change (∀ _ : Unit, (𝟙 B ≫ q).app n s ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C).obj n) ↔
      q.app n s ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C).obj n
    simp only [Category.id_comp, forall_const]
  rw [← he]
  infer_instance

variable {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}

local notation "W" => (Subcomplex.preimage (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C.obj) q.hom : SSet)
local notation "Q" => Subcomplex.fromPreimage (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C.obj) q.hom

/-- 終対象付き右ファイブレーションへの同じ引き戻し内で、任意の有限図式に実錐がある。 -/
lemma exists_verdierCorePullback_finiteCone (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q)
    {Y : SSet.{u}} [Quasicategory Y] (r : Y ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C.obj : SSet.{u}))
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration r] {y : Y _⦋0⦌} (hy : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex y)
    {K : SSet.{u}} [K.Finite] (a : K ⟶ pullback Q r) : Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone a) := by
  let : Quasicategory W := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.corePreimage_quasicategory q.hom
  let coreι := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C.obj).ι
  let P := (a ≫ pullback.fst Q r) ≫ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C.obj).preimage q.hom).ι
  let γ := a ≫ pullback.snd Q r
  let R := r ≫ coreι
  have hγ : P ≫ q.hom = γ ≫ R := by
    change ((a ≫ pullback.fst Q r) ≫ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C.obj).preimage q.hom).ι) ≫ q.hom = _
    change ((a ≫ pullback.fst Q r) ≫ Q) ≫ coreι = _
    have he : pullback.fst Q r ≫ Q = pullback.snd Q r ≫ r := pullback.condition
    simpa only [γ, R, Category.assoc] using congrArg (fun k => a ≫ k ≫ coreι) he
  have hY := rightFibration_isContractibleKan_of_terminal r hy
  obtain ⟨G, hG⟩ := (hY.isInitialVertex y).exists_cosliceLift γ
  let cY : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone γ := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry G, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceUnderUncurry_projection G).trans hG⟩
  let t : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (P ≫ q.hom) := ⟨cY.val ≫ R, by
    rw [← Category.assoc, cY.property]
    exact hγ.symm⟩
  obtain ⟨c, ⟨e⟩⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.exists_verdierQuotientConeIsoRefinement h P t
  have hInv : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges (c.val ≫ q.hom) Set.univ := by
    have hcIso := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneFunctorIsoOfVertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone q.hom c) t e
    exact (invertsEdges_functorIso_iff hcIso Set.univ).mpr
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertsAllEdges_toKan (cY.val ≫ r)).comp coreι)
  let cWval := corePreimageLift q.hom c.val hInv
  have hcW : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) K ≫ cWval = a ≫ pullback.fst Q r := by
    apply (cancel_mono ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C.obj).preimage q.hom).ι).mp
    rw [Category.assoc, corePreimageLift_ι, c.property]
  let cW : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (a ≫ pullback.fst Q r) := ⟨cWval, hcW⟩
  let cQ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (γ ≫ R) := ⟨c.val ≫ q.hom, by
    rw [← Category.assoc, c.property, hγ]⟩
  obtain ⟨v, hv⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective
    (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (P ≫ q.hom)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone q.hom c) t e.hom
  have hvInv : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (P ≫ q.hom)) v := by
    change IsIso (Truncated.HomotopyCategory.homMk v)
    rw [hv]
    infer_instance
  obtain ⟨v', hv'⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exists_coneEdge_rebase_of_val_eq v
    (show (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone q.hom c).val = cQ.val from rfl)
    (show t.val = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone R cY).val from rfl)
  have hv'Inv : IsIso (Truncated.HomotopyCategory.homMk v') := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.derived_rightFibration_reflects_invertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (γ ≫ R)) v'
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr hv').mpr
      (hvInv.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (P ≫ q.hom)))
  have hr : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting r := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightFibration_equivalenceLifting r
  have hι : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting coreι := coreInclusion_equivalenceLifting C.obj
  have hR : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting R := by
    intro U V j hm he
    have := hr j hm he
    have := hι j hm he
    infer_instance
  have hs : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp γ R) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.sliceOverPostcomp_equivalenceLifting γ R hR
  obtain ⟨dY, hdY, _⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.exists_kanVertexIso_lift_target
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp γ R) hs cY cQ (asIso (Truncated.HomotopyCategory.homMk v'))
  have hdYval : dY.val ≫ R = c.val ≫ q.hom := congrArg Subtype.val hdY
  have hpair : cW.val ≫ Q = dY.val ≫ r := by
    apply (cancel_mono coreι).mp
    change (cWval ≫ Q) ≫ coreι = (dY.val ≫ r) ≫ coreι
    change (cWval ≫ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C.obj).preimage q.hom).ι) ≫ q.hom = _
    rw [corePreimageLift_ι]
    exact hdYval.symm
  let F := pullback.lift cW.val dY.val hpair
  refine ⟨⟨F, ?_⟩⟩
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst]
    exact cW.property
  · rw [Category.assoc, pullback.lift_snd]
    exact dY.property

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
