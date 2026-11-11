module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CosliceRetractionComparison

/-!
概要：定値な底を持つ同じ余錐族の二つの切断での値を、底を保って比較する。
方針：元の族と一方の切断から戻した族との同じ円柱を、もう一方へ制限する。
規約：底と可変終点を全時刻固定する。使われ方：時間零・一の初期 Hom 族の接続。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
noncomputable section
variable {K L E B T : SSet.{u}} (d : L ⟶ E) (r : K ⟶ L) (s : L ⟶ K)
  (hs : s ≫ r = 𝟙 L) [Mono s] (hsr : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions s)
  (q : E ⟶ B) [InnerFibration q] (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (r ≫ d))
  (b : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (d ≫ q))
  (hb : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp (r ≫ d) q = b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict (d ≫ q) r)
  (s' : L ⟶ K) (hs' : s' ≫ r = 𝟙 L)
local notation "P" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction (r ≫ d) s
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceRetractionFamily_diagram d r s hs)
local notation "P'" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction (r ≫ d) s'
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceRetractionFamily_diagram d r s' hs')
local notation "H" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceRetractionFamilyComparison d r s hs hsr q a b hb

/-- 同じ全族の二つの切断での値を、実際の円柱で接続する。 -/
def cosliceRetractionSectionComparison : SSet.Homotopy (a ≫ P') (a ≫ P) where
  h := (H).h ≫ P'
  h₀ := by
    change SSet.ι₀ ≫ ((H).h ≫ P') = a ≫ P'
    rw [← Category.assoc, (H).h₀]
  h₁ := by
    change SSet.ι₁ ≫ ((H).h ≫ P') = a ≫ P
    rw [← Category.assoc, (H).h₁,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceRetractionFamily_other_section d r s hs a s' hs']
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 二切断の比較は、同じ収縮比較を同じもう一方の切断へ制限した raw な円柱。 -/
lemma cosliceRetractionSectionComparison_raw :
    (cosliceRetractionSectionComparison d r s hs hsr q a b hb s' hs').h = (H).h ≫ P' := rfl

/-- 比較の底は、一方の切断での元の底の全族で全時刻固定する。 -/
lemma cosliceRetractionSectionComparison_base :
    (cosliceRetractionSectionComparison d r s hs hsr q a b hb s' hs').h ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp d q = fst T Δ[1] ≫ (a ≫ P') ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp d q := by
  change ((H).h ≫ P') ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp d q = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction_postcomp_family,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceRetractionFamilyComparison_base]
  have h := congrArg (fun m ↦ fst T (Δ[1] : SSet.{u}) ≫ m)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction_postcomp_family (r ≫ d) s' d
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceRetractionFamily_diagram d r s' hs') q a)
  simpa only [Category.assoc] using h.symm

/-- 二切断の比較も、元の可変終点の全族を全時刻保持する。 -/
lemma cosliceRetractionSectionComparison_projection :
    (cosliceRetractionSectionComparison d r s hs hsr q a b hb s' hs').h ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection d = fst T Δ[1] ≫ a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (r ≫ d) := by
  rw [cosliceRetractionSectionComparison, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction_projection, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceRetractionFamilyComparison_projection]

end
end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
