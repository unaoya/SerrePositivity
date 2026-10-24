module

public import SerrePositivity.InfinityCategories.F2.Presentable.ColimitFromLocalLeftKan
public import SerrePositivity.InfinityCategories.F1B.KanExtension.LeftCommaCoconeColimit
public import SerrePositivity.InfinityCategories.F1B.KanExtension.LeftHomUniversal
public import SerrePositivity.InfinityCategories.Core.ColimitDiagramIso

/-!
概要：元の図式とその全左 Kan 延長の余極限の存在を比較する。
方針：同じ comma の相対 join の両端で全余錐の同値を使い、元の延長との同型で戻す。
規約：どちらの余極限の存在も相手の仮定に混入させない。
使われ方：P_Σ 内の表現可能生成図式と、その次数・密度余極限の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：全余錐制限の同値は余極限の存在を両方向に移す。
方針：普遍余錐の制限と同値の逆による存在を合わせる。
規約：指定図式と同じ制限を使う。
使われ方：相対 join の両端における余極限の存在の比較。 -/
lemma hasColimit_iff_restrict_of_sliceUnderEquivalence
    {A B X : SSet.{u}} [Quasicategory X] (i : A ⟶ B) (F : B ⟶ X)
    (he : IsQCatEquivalence (sliceUnderRestrict F i)) :
    HasColimit F ↔ HasColimit (i ≫ F) := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c.restrict i, (he.choose.isInitialVertex_iff c).mp hc⟩
  · exact hasColimit_of_sliceUnderRestrict_equivalence i F he

/-- 概要：comma の普遍な候補の余極限の存在は元の図式の余極限の存在と同値。
方針：相対 join の普遍な左端・任意の右端・元の comma 包含の三つの同値を合成する。
規約：候補の元の左端の等式と全 fiber の普遍性を明示する。
使われ方：任意の指定左 Kan 延長への余極限の存在の移送。 -/
lemma leftCommaCandidate_hasColimit_iff
    {A B X : SSet.{u}} [Quasicategory A] [Quasicategory B] [Quasicategory X]
    (δ : A ⟶ B) (F : A ⟶ X)
    (H : relativeJoin (F1B.kanLeftCommaProjection δ) (𝟙 B) ⟶ X)
    (hH : relativeJoinInl (F1B.kanLeftCommaProjection δ) (𝟙 B) ≫ H =
      F1B.kanLeftCommaSource δ ≫ F)
    (hcol : ∀ b, IsColimitCone
      (F1B.kanRelativeJoinFiberCocone (F1B.kanLeftCommaProjection δ) b H)) :
    HasColimit (F1B.kanLeftCommaCandidate δ H) ↔ HasColimit F := by
  have hr := hasColimit_iff_restrict_of_sliceUnderEquivalence
    (relativeJoinInr (F1B.kanLeftCommaProjection δ) (𝟙 B)) H
    (relativeJoinRight_sliceUnderRestrict_equivalence (F1B.kanLeftCommaProjection δ) H)
  have hl := hasColimit_iff_restrict_of_sliceUnderEquivalence
    (relativeJoinInl (F1B.kanLeftCommaProjection δ) (𝟙 B)) H
    (Ind.sliceUnderRestrict_isQCatEquivalence_of_initialBoundary H _
      (F1B.kanRelativeJoinFunctor_initialBoundary_of_colimit_fibers
        (F1B.kanLeftCommaProjection δ) H hcol))
  rw [hH] at hl
  have hs := hasColimit_iff_restrict_of_sliceUnderEquivalence
    (F1B.kanLeftCommaInclusion δ) (F1B.kanLeftCommaSource δ ≫ F)
    (commaSource_sliceUnderRestrict_equivalence δ F)
  have he : F1B.kanLeftCommaInclusion δ ≫ (F1B.kanLeftCommaSource δ ≫ F) = F := by
    rw [← Category.assoc, F1B.kanLeftCommaInclusion_source, Category.id_comp]
  rw [he] at hs
  exact hr.symm.trans (hl.trans hs)

/-- 概要：元の全左 Kan 延長の余極限の存在は、元の図式の余極限の存在と同値。
方針：同じ局所余極限で構成した comma 候補と指定延長の関手同型を使う。
規約：元の指定単位を保った左 Kan 条件を入力とする。
使われ方：bar 図式の反映と simplicial Ind 表示への接続。 -/
lemma hasColimit_iff_leftKanExtension
    {A B X : SSet.{u}} [Quasicategory A] [Quasicategory B] [Quasicategory X]
    (δ : A ⟶ B) {F : A ⟶ X} {G : B ⟶ X}
    (β : SSet.Homotopy F (δ ≫ G)) (hβ : IsLeftKanExtension δ F G β) :
    HasColimit G ↔ HasColimit F := by
  have hlocal : ∀ b, HasColimit (leftKanDiagram δ F b) := by
    intro b
    obtain ⟨c, hc, _⟩ := hβ.colimitValue b
    exact ⟨c, hc⟩
  obtain ⟨H, hH, _, hcol⟩ := F1B.exists_kanLeftComma_candidate δ F hlocal
  let γ := F1B.kanLeftCommaCandidateTransformation δ F H hH
  have hγ := F1B.kanLeftCommaCandidate_isLeftKanExtension δ F H hH hcol
  let e := F1B.kanLeftKanExtensionIso δ γ β hγ hβ
  exact (hasColimit_iff_of_functorIso e).symm.trans
    (leftCommaCandidate_hasColimit_iff δ F H hH hcol)

end SerrePositivity.InfinityCategories.F2.Presentable
