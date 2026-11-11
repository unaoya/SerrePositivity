module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.CompactInputComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CosliceTrivialFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.EquivalenceLimits

/-!
概要：入力と標的を固定する後合成の恒等・合成・自明 Kan 保存。
方針：全余錐の展開と既存の固定始域後合成の合成則を使う。
規約：固定図式を全単体上の等式で保持する。
使われ方：Ind 底で構成した比較同型を元の底へ厳密に戻す。

対応節は Kerodon 9.4（Tag 06GT）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility

/-- 概要：元の固定始域を保持する恒等後合成は恒等射。
方針：元の全余錐族の展開を比較する。
規約：元の全図式を変更しない。
使われ方：元の底への切断と射影の合成の相殺。 -/
lemma stableInputCoslice_id {K C : SSet.{u}} (q : K ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableCoslicePostcomp q (𝟙 C) q (Category.comp_id q) = 𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder q) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_injective q
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableCoslicePostcomp_uncurry q (𝟙 C) q (Category.comp_id q) (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder q))
  simpa only [Category.id_comp, Category.comp_id] using h

/-- 概要：入力と標的を固定する恒等後合成は恒等射。
方針：同じ全増大図式の展開を比較する。
規約：元の入力と標的をそのまま保持する。
使われ方：元の底への回収後の同じ頂点の相殺。 -/
lemma stableInputPostcomp_id {K C : SSet.{u}} (q : K ⟶ C) (z : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone q) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.stableInputPostcomp q (𝟙 C) q (Category.comp_id q) z z (Category.comp_id z.val) = 𝟙 _ := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_injective ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder q)).symm z)
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.stableInputPostcomp_uncurry q (𝟙 C) q (Category.comp_id q) z z
    (Category.comp_id z.val) (𝟙 _)
  simpa only [Category.id_comp, stableInputCoslice_id, Category.comp_id] using h

/-- 概要：入力と標的を固定する二段階の後合成は合成関手による一段階の後合成。
方針：全増大図式の展開と既存の固定始域後合成の合成則を使う。
規約：各段の表示の等号はそのまま保持する。
使われ方：共通解像への切断と元の底への射影の相殺。 -/
lemma stableInputPostcomp_comp {K C B E : SSet.{u}}
    (q : K ⟶ C) (f : C ⟶ B) (r : K ⟶ B) (hq : q ≫ f = r)
    (g : B ⟶ E) (s : K ⟶ E) (hr : r ≫ g = s)
    (z : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone q) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone r) (v : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone s)
    (hz : z.val ≫ f = t.val) (ht : t.val ≫ g = v.val) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.stableInputPostcomp q f r hq z t hz ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.stableInputPostcomp r g s hr t v ht =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.stableInputPostcomp q (f ≫ g) s (by rw [← Category.assoc, hq, hr]) z v
        (by rw [← Category.assoc, hz, ht]) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_injective ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder s)).symm v)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.stableInputPostcomp_uncurry]
  have hf := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.stableInputPostcomp_uncurry q f r hq z t hz (𝟙 _)
  rw [Category.id_comp] at hf
  rw [hf, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableCoslicePostcomp_comp]
  have hfg := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.stableInputPostcomp_uncurry q (f ≫ g) s
    (by rw [← Category.assoc, hq, hr]) z v (by rw [← Category.assoc, hz, ht]) (𝟙 _)
  simpa only [Category.id_comp] using hfg.symm

/-- 概要：自明 Kan 射による入力固定の二重後合成も自明 Kan 射。
方針：元の coslice と slice の後合成の自明 Kan 保存と表示同型を合成する。
規約：固定図式の大きさや圏の充填性を追加仮定にしない。
使われ方：Ind 比較同型を共通解像へ持ち上げる。 -/
lemma stableInputPostcomp_trivialKanFibration {K C B : SSet.{u}}
    (q : K ⟶ C) (f : C ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration f]
    (r : K ⟶ B) (hq : q ≫ f = r) (z : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone q) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone r)
    (hz : z.val ≫ f = t.val) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.stableInputPostcomp q f r hq z t hz) := by
  have hu := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CosliceTrivialFibration.sliceUnderPostcomp_trivialKanFibration q f
  have hR : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableCoslicePostcomp q f r hq) :=
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations.comp_mem _ _ hu.mem (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations.of_isIso _)⟩
  have ho : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp
      ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder q)).symm z) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableCoslicePostcomp q f r hq)) :=
    inferInstance
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.stableInputPostcomp]
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations.comp_mem _ _ ho.mem (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations.of_isIso _)⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility
