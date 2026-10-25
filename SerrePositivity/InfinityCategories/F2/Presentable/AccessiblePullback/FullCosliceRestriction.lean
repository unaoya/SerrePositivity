module

public import SerrePositivity.InfinityCategories.F2.Compact.FullCoslicePullback
public import SerrePositivity.InfinityCategories.F2.Presentable.PredicatePreimagePullback

/-!
概要：全部分圏内の全 coslice を、周囲の全 coslice の同じ頂点条件の全部分圏と厳密に比較する。
方針：二つの既存の実引き戻しの比較同型を合成する。
規約：図式の colimit の存在を要求せず、元の全単体と射影を保持する。
使われ方：前層模型で因子化した全余錐と比較辺の元の accessible 圏への回収。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback

/-- 概要：全部分圏内の coslice は周囲の同じ coslice の頂点条件による全部分圏と同型。
方針：同じ底の包含に沿う二つの実引き戻しを比較する。
規約：元の図式と余錐頂点の条件を固定する。
使われ方：周囲で作った余錐の厳密な持ち上げ。 -/
def fullCosliceRestrictionIso {K X : SSet.{u}} (P : X _⦋0⦌ → Prop)
    (q : K ⟶ (fullSubcomplexOnVertices X P : SSet.{u})) :
    sliceUnder q ≅
      (fullSubcomplexOnVertices
        (sliceUnder (q ≫ (fullSubcomplexOnVertices X P).ι))
        (fun c ↦ P ((sliceUnderProjection (q ≫ (fullSubcomplexOnVertices X P).ι)).app _ c)) :
        SSet.{u}) :=
  (Compact.fullSliceUnder_isPullback P q).isoPullback ≪≫
    (predicatePreimage_isPullback
      (sliceUnderProjection (q ≫ (fullSubcomplexOnVertices X P).ι)) P).flip.isoPullback.symm

/-- 概要：同じ coslice 同型を周囲へ含めると元の後合成を厳密に回収する。
方針：二つの実引き戻し比較の同じ第二脚を計算する。
規約：余錐の図式と比較辺を変更しない。
使われ方：全余錐と元の比較の射影公式。 -/
lemma fullCosliceRestrictionIso_hom_inclusion {K X : SSet.{u}} (P : X _⦋0⦌ → Prop)
    (q : K ⟶ (fullSubcomplexOnVertices X P : SSet.{u})) :
    (fullCosliceRestrictionIso P q).hom ≫
      (fullSubcomplexOnVertices
        (sliceUnder (q ≫ (fullSubcomplexOnVertices X P).ι))
        (fun c ↦ P ((sliceUnderProjection (q ≫ (fullSubcomplexOnVertices X P).ι)).app _ c))).ι =
      sliceUnderPostcomp q (fullSubcomplexOnVertices X P).ι := by
  rw [fullCosliceRestrictionIso, Iso.trans_hom, Iso.symm_hom]
  rw [Category.assoc,
    (predicatePreimage_isPullback
      (sliceUnderProjection (q ≫ (fullSubcomplexOnVertices X P).ι)) P).flip.isoPullback_inv_snd]
  exact (Compact.fullSliceUnder_isPullback P q).isoPullback_hom_snd

end SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
