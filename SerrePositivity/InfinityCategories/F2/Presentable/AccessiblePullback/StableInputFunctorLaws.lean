module

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.CompactInputComparison
public import SerrePositivity.InfinityCategories.F1B.Cones.CosliceTrivialFibration
public import SerrePositivity.InfinityCategories.Core.EquivalenceLimits

/-!
概要：入力と標的を固定する後合成の恒等・合成・自明 Kan 保存。
方針：全余錐の展開と既存の固定始域後合成の合成則を使う。
規約：固定図式を全単体上の等式で保持する。
使われ方：Ind 底で構成した比較同型を元の底へ厳密に戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback

/-- 概要：元の固定始域を保持する恒等後合成は恒等射。
方針：元の全余錐族の展開を比較する。
規約：元の全図式を変更しない。
使われ方：元の底への切断と射影の合成の相殺。 -/
lemma stableInputCoslice_id {K C : SSet.{u}} (q : K ⟶ C) :
    stableCoslicePostcomp q (𝟙 C) q (Category.comp_id q) = 𝟙 (sliceUnder q) := by
  apply sliceUnderUncurry_injective q
  have h := stableCoslicePostcomp_uncurry q (𝟙 C) q (Category.comp_id q) (𝟙 (sliceUnder q))
  simpa only [Category.id_comp, Category.comp_id] using h

/-- 概要：入力と標的を固定する恒等後合成は恒等射。
方針：同じ全増大図式の展開を比較する。
規約：元の入力と標的をそのまま保持する。
使われ方：元の底への回収後の同じ頂点の相殺。 -/
lemma stableInputPostcomp_id {K C : SSet.{u}} (q : K ⟶ C) (z : JoinCocone q) :
    stableInputPostcomp q (𝟙 C) q (Category.comp_id q) z z (Category.comp_id z.val) = 𝟙 _ := by
  apply sliceOverUncurry_injective ((SSet.yonedaEquiv (X := sliceUnder q)).symm z)
  have h := stableInputPostcomp_uncurry q (𝟙 C) q (Category.comp_id q) z z
    (Category.comp_id z.val) (𝟙 _)
  simpa only [Category.id_comp, stableInputCoslice_id, Category.comp_id] using h

/-- 概要：入力と標的を固定する二段階の後合成は合成関手による一段階の後合成。
方針：全増大図式の展開と既存の固定始域後合成の合成則を使う。
規約：各段の表示の等号はそのまま保持する。
使われ方：共通解像への切断と元の底への射影の相殺。 -/
lemma stableInputPostcomp_comp {K C B E : SSet.{u}}
    (q : K ⟶ C) (f : C ⟶ B) (r : K ⟶ B) (hq : q ≫ f = r)
    (g : B ⟶ E) (s : K ⟶ E) (hr : r ≫ g = s)
    (z : JoinCocone q) (t : JoinCocone r) (v : JoinCocone s)
    (hz : z.val ≫ f = t.val) (ht : t.val ≫ g = v.val) :
    stableInputPostcomp q f r hq z t hz ≫ stableInputPostcomp r g s hr t v ht =
      stableInputPostcomp q (f ≫ g) s (by rw [← Category.assoc, hq, hr]) z v
        (by rw [← Category.assoc, hz, ht]) := by
  apply sliceOverUncurry_injective ((SSet.yonedaEquiv (X := sliceUnder s)).symm v)
  rw [stableInputPostcomp_uncurry]
  have hf := stableInputPostcomp_uncurry q f r hq z t hz (𝟙 _)
  rw [Category.id_comp] at hf
  rw [hf, Category.assoc, stableCoslicePostcomp_comp]
  have hfg := stableInputPostcomp_uncurry q (f ≫ g) s
    (by rw [← Category.assoc, hq, hr]) z v (by rw [← Category.assoc, hz, ht]) (𝟙 _)
  simpa only [Category.id_comp] using hfg.symm

/-- 概要：自明 Kan 射による入力固定の二重後合成も自明 Kan 射。
方針：元の coslice と slice の後合成の自明 Kan 保存と表示同型を合成する。
規約：固定図式の大きさや圏の充填性を追加仮定にしない。
使われ方：Ind 比較同型を共通解像へ持ち上げる。 -/
lemma stableInputPostcomp_trivialKanFibration {K C B : SSet.{u}}
    (q : K ⟶ C) (f : C ⟶ B) [TrivialKanFibration f]
    (r : K ⟶ B) (hq : q ≫ f = r) (z : JoinCocone q) (t : JoinCocone r)
    (hz : z.val ≫ f = t.val) :
    TrivialKanFibration (stableInputPostcomp q f r hq z t hz) := by
  have hu := F1B.sliceUnderPostcomp_trivialKanFibration q f
  have hR : TrivialKanFibration (stableCoslicePostcomp q f r hq) :=
    ⟨trivialKanFibrations.comp_mem _ _ hu.mem (trivialKanFibrations.of_isIso _)⟩
  have ho : TrivialKanFibration (sliceOverPostcomp
      ((SSet.yonedaEquiv (X := sliceUnder q)).symm z) (stableCoslicePostcomp q f r hq)) :=
    inferInstance
  dsimp only [stableInputPostcomp]
  exact ⟨trivialKanFibrations.comp_mem _ _ ho.mem (trivialKanFibrations.of_isIso _)⟩

end SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
