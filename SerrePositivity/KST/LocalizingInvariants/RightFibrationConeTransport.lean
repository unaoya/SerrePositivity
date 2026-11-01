module

public import SerrePositivity.InfinityCategories.Derived.SliceCornerRightFibration
public import SerrePositivity.InfinityCategories.Core.RightFibrationContractible
public import SerrePositivity.InfinityCategories.Core.RightFibrationReflection
public import SerrePositivity.InfinityCategories.Core.EquivalenceTerminal

/-!
概要：右ファイブレーション上の全錐を、指定された同じ底の錐比較に沿って輸送する。
方針：slice の corner と元の右ファイブレーションの引き戻しを合成する。
規約：形状の可縮性は要求しない。終対象付きの場合の可縮性も元の実辺から証明する。
使われ方：零次商比較の slice 内の有限錐を、回収済みの元の全錐へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

lemma sliceOverPostcomp_rightFibration {K E B : SSet.{u}} (a : K ⟶ E)
    (r : E ⟶ B) [RightFibration r] : RightFibration (sliceOverPostcomp a r) := by
  have : RightFibration (pullback.fst (sliceOverProjection (a ≫ r)) r) :=
    ⟨rightFibrations.pullback_fst _ _ (RightFibration.mem (p := r))⟩
  have h : RightFibration (sliceOverCornerMap a r ≫
      pullback.fst (sliceOverProjection (a ≫ r)) r) :=
    ⟨rightFibrations.comp_mem _ _ RightFibration.mem RightFibration.mem⟩
  have he : sliceOverCornerMap a r ≫ pullback.fst (sliceOverProjection (a ≫ r)) r =
      sliceOverPostcomp a r := pullback.lift_fst _ _ _
  exact he ▸ h

/-- Kan 基底への右ファイブレーションの終対象は、元の全空間の可縮 Kan 性を与える。 -/
lemma rightFibration_isContractibleKan_of_terminal {E B : SSet.{u}}
    [Quasicategory E] [KanComplex B] (r : E ⟶ B) [RightFibration r]
    {t : E _⦋0⦌} (ht : IsTerminalVertex t) : IsContractibleKan E := by
  apply isContractibleKan_of_nonempty_of_all_terminal ⟨t⟩
  intro y
  obtain ⟨e⟩ := ht.nonempty_edge y
  have hmap : IsInvertibleEdge (e.map ((truncation 2).map r)) :=
    @IsGroupoid.all_isIso (hoFunctor.obj B) _ (kanComplex_ho_isGroupoid B) _ _ _
  have he : IsIso (Truncated.HomotopyCategory.homMk e) :=
    derived_rightFibration_reflects_invertibleEdge r e hmap
  exact ht.of_vertexIso (asIso (Truncated.HomotopyCategory.homMk e)).symm

end SerrePositivity.KST.LocalizingInvariants
