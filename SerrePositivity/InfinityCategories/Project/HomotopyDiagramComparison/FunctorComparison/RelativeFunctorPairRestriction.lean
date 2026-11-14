module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FunctorComparison.RelativeFunctorCoprodPair
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.RelativeFunctorRestrictionFibration

/-!
概要：互いに交わらない二部分の同時制限を、余積形状への制限で構成する。
方針：両枝の raw な族を貼り、余積包含による制限の持ち上げを使う。
規約：結合した包含の単射性を明示する。使われ方：初期値固定の終点評価の充填性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
attribute [local irreducible] _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorCurry _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry
variable {A D C E B : SSet.{u}} (p : E ⟶ B) (β : A ⟶ B) (i : D ⟶ A) (j : C ⟶ A)

/-- 二部分の相対族を、同じ底を保って同時に制限する。 -/
def relativeFunctorPairRestriction : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p β ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p (i ≫ β) ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p (j ≫ β) :=
  lift (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p β i) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p β j)

/-- 余積形状への制限が持ち上げる射は、二部分の同時制限でも持ち上げる。 -/
lemma relativeFunctorPairRestriction_hasLiftingProperty {T U : SSet.{u}} (r : T ⟶ U)
    [HasLiftingProperty r (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p β (coprod.desc i j))] :
    HasLiftingProperty r (relativeFunctorPairRestriction p β i j) := by
  constructor
  intro a b sq
  let m := coprod.desc i j
  let G := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coprodTensorGlue (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (b ≫ fst _ _))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (b ≫ snd _ _))
  have hG : G ≫ p = fst (D ⨿ C) U ≫ (m ≫ β) := by
    apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coprodTensor_hom_ext
    · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coprodTensorGlue_inl, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_projection,
        whiskerRight_fst_assoc, ← Category.assoc coprod.inl, coprod.inl_desc]
    · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coprodTensorGlue_inr, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_projection,
        whiskerRight_fst_assoc, ← Category.assoc coprod.inr, coprod.inr_desc]
  let b' := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorCurry G hG
  have h₀ : (coprod.inl ▷ U) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry b' =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (b ≫ fst _ _) := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_curry, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coprodTensorGlue_inl]
  have h₁ : (coprod.inr ▷ U) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry b' =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (b ≫ snd _ _) := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_curry, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coprodTensorGlue_inr]
  have ha₀ : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p β i = r ≫ (b ≫ fst _ _) := by
    simpa only [relativeFunctorPairRestriction, Category.assoc, lift_fst] using
      congrArg (fun t ↦ t ≫ fst _ _) sq.w
  have ha₁ : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p β j = r ≫ (b ≫ snd _ _) := by
    simpa only [relativeFunctorPairRestriction, Category.assoc, lift_snd] using
      congrArg (fun t ↦ t ≫ snd _ _) sq.w
  have hs : CommSq a r (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p β m) b' := by
    constructor
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_injective p (m ≫ β)
    apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coprodTensor_hom_ext
    · calc
        _ = (i ▷ T) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry a := by
          rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorUncurry_pre, ← Category.assoc,
            ← MonoidalCategory.comp_whiskerRight, coprod.inl_desc]
        _ = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p β i) :=
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorUncurry_pre a i).symm
        _ = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (r ≫ (b ≫ fst _ _)) := congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry ha₀
        _ = (D ◁ r) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (b ≫ fst _ _) :=
          _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorUncurry_parameter (b ≫ fst _ _) r
        _ = _ := by
          rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorUncurry_parameter b' r,
            ← Category.assoc, ← whisker_exchange,
            Category.assoc, h₀]
    · calc
        _ = (j ▷ T) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry a := by
          rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorUncurry_pre, ← Category.assoc,
            ← MonoidalCategory.comp_whiskerRight, coprod.inr_desc]
        _ = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p β j) :=
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorUncurry_pre a j).symm
        _ = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (r ≫ (b ≫ snd _ _)) := congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry ha₁
        _ = (C ◁ r) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (b ≫ snd _ _) :=
          _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorUncurry_parameter (b ≫ snd _ _) r
        _ = _ := by
          rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorUncurry_parameter b' r,
            ← Category.assoc, ← whisker_exchange,
            Category.assoc, h₁]
  refine CommSq.HasLift.mk' { l := hs.lift, fac_left := hs.fac_left, fac_right := ?_ }
  apply CartesianMonoidalCategory.hom_ext
  · change hs.lift ≫ relativeFunctorPairRestriction p β i j ≫ fst _ _ = b ≫ fst _ _
    rw [relativeFunctorPairRestriction, lift_fst]
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_injective p (i ≫ β)
    have h := congrArg (fun t ↦ (coprod.inl ▷ U) ≫ t)
      (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry hs.fac_right)
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorUncurry_pre, ← Category.assoc,
      ← MonoidalCategory.comp_whiskerRight, coprod.inl_desc, h₀] at h
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorUncurry_pre hs.lift i).trans h
  · change hs.lift ≫ relativeFunctorPairRestriction p β i j ≫ snd _ _ = b ≫ snd _ _
    rw [relativeFunctorPairRestriction, lift_snd]
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_injective p (j ≫ β)
    have h := congrArg (fun t ↦ (coprod.inr ▷ U) ≫ t)
      (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry hs.fac_right)
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorUncurry_pre, ← Category.assoc,
      ← MonoidalCategory.comp_whiskerRight, coprod.inr_desc, h₁] at h
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorUncurry_pre hs.lift j).trans h

/-- 結合した包含が単射なら、二部分の同時制限は left fibration である。 -/
instance relativeFunctorPairRestriction_leftFibration [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
    [Mono (coprod.desc i j)] : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (relativeFunctorPairRestriction p β i j) where
  mem := by
    intro T U r hr
    have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p β (coprod.desc i j)) r hr
    exact relativeFunctorPairRestriction_hasLiftingProperty p β i j r

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
