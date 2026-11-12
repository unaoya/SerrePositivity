module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CommaSourceColimits
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.RelativeJoinRightColimits
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftCommaCandidate
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeJoinFunctorInitialBoundary
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.InitialBoundaryCoconeRestriction

/-!
概要：各局所左 Kan 図式の余極限と延長先の余極限から元の余極限を構成する。
方針：comma の相対 join 上で普遍な図式を構成し、両端への余錐制限を比較する。
規約：元の図式の余極限の存在を入力にしない。
使われ方：次数ごとの小余積と幾何学的実現の合成による小余極限。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：全局所余極限が存在し、延長先形状の余極限があれば、元の図式に余極限が存在する。
方針：同じ comma 候補の右端の余極限を全相対 join へ戻し、普遍な左端へ制限する。
規約：元の形状と図式を保ち、元の余極限の存在は仮定しない。
使われ方：小余積と幾何学的実現からの小余極限の一般構成。 -/
lemma hasColimit_of_localLeftKan_colimits
    {A B X : SSet.{u}} [Quasicategory A] [Quasicategory B] [Quasicategory X]
    (δ : A ⟶ B) (F : A ⟶ X)
    (hlocal : ∀ b, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram δ F b))
    (hB : ∀ G : B ⟶ X, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit G) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit F := by
  obtain ⟨H, hH, _, hcol⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanLeftComma_candidate δ F hlocal
  have hh : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit H := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.relativeJoin_hasColimit_of_right
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ) H (hB (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaCandidate δ H))
  obtain ⟨c, hc⟩ := hh
  have hb := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinFunctor_initialBoundary_of_colimit_fibers
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ) H hcol
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.sliceUnderRestrict_isQCatEquivalence_of_initialBoundary H
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ) (𝟙 B)) hb
  have hc' := (he.choose.isInitialVertex_iff c).mp hc
  have hl : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ) (𝟙 B) ≫ H) :=
    ⟨c.restrict _, hc'⟩
  rw [hH] at hl
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.hasColimit_of_commaSource δ F hl

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
