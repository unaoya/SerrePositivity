module

public import SerrePositivity.InfinityCategories.F2.Presentable.CommaSourceColimits
public import SerrePositivity.InfinityCategories.F2.Presentable.RelativeJoinRightColimits
public import SerrePositivity.InfinityCategories.F1B.KanExtension.LeftCommaCandidate
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeJoinFunctorInitialBoundary
public import SerrePositivity.InfinityCategories.F1.Ind.InitialBoundaryCoconeRestriction

/-!
概要：各局所左 Kan 図式の余極限と延長先の余極限から元の余極限を構成する。
方針：comma の相対 join 上で普遍な図式を構成し、両端への余錐制限を比較する。
規約：元の図式の余極限の存在を入力にしない。
使われ方：次数ごとの小余積と幾何学的実現の合成による小余極限。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：全局所余極限が存在し、延長先形状の余極限があれば、元の図式に余極限が存在する。
方針：同じ comma 候補の右端の余極限を全相対 join へ戻し、普遍な左端へ制限する。
規約：元の形状と図式を保ち、元の余極限の存在は仮定しない。
使われ方：小余積と幾何学的実現からの小余極限の一般構成。 -/
lemma hasColimit_of_localLeftKan_colimits
    {A B X : SSet.{u}} [Quasicategory A] [Quasicategory B] [Quasicategory X]
    (δ : A ⟶ B) (F : A ⟶ X)
    (hlocal : ∀ b, HasColimit (leftKanDiagram δ F b))
    (hB : ∀ G : B ⟶ X, HasColimit G) : HasColimit F := by
  obtain ⟨H, hH, _, hcol⟩ := F1B.exists_kanLeftComma_candidate δ F hlocal
  have hh : HasColimit H := relativeJoin_hasColimit_of_right
    (F1B.kanLeftCommaProjection δ) H (hB (F1B.kanLeftCommaCandidate δ H))
  obtain ⟨c, hc⟩ := hh
  have hb := F1B.kanRelativeJoinFunctor_initialBoundary_of_colimit_fibers
    (F1B.kanLeftCommaProjection δ) H hcol
  have he := Ind.sliceUnderRestrict_isQCatEquivalence_of_initialBoundary H
    (relativeJoinInl (F1B.kanLeftCommaProjection δ) (𝟙 B)) hb
  have hc' := (he.choose.isInitialVertex_iff c).mp hc
  have hl : HasColimit (relativeJoinInl (F1B.kanLeftCommaProjection δ) (𝟙 B) ≫ H) :=
    ⟨c.restrict _, hc'⟩
  rw [hH] at hl
  exact hasColimit_of_commaSource δ F hl

end SerrePositivity.InfinityCategories.F2.Presentable
