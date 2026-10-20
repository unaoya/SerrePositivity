module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CosliceRetractionComparison

/-!
概要：定値な底を持つ同じ余錐族の二つの切断での値を、底を保って比較する。
方針：元の族と一方の切断から戻した族との同じ円柱を、もう一方へ制限する。
規約：底と可変終点を全時刻固定する。使われ方：時間零・一の初期 Hom 族の接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {K L E B T : SSet.{u}} (d : L ⟶ E) (r : K ⟶ L) (s : L ⟶ K)
  (hs : s ≫ r = 𝟙 L) [Mono s] (hsr : rightAnodyneExtensions s)
  (q : E ⟶ B) [InnerFibration q] (a : T ⟶ sliceUnder (r ≫ d))
  (b : T ⟶ sliceUnder (d ≫ q))
  (hb : a ≫ sliceUnderPostcomp (r ≫ d) q = b ≫ sliceUnderRestrict (d ≫ q) r)
  (s' : L ⟶ K) (hs' : s' ≫ r = 𝟙 L)
local notation "P" => normalizedCoconeRestriction (r ≫ d) s
  (cosliceRetractionFamily_diagram d r s hs)
local notation "P'" => normalizedCoconeRestriction (r ≫ d) s'
  (cosliceRetractionFamily_diagram d r s' hs')
local notation "H" => cosliceRetractionFamilyComparison d r s hs hsr q a b hb

/-- 同じ全族の二つの切断での値を、実際の円柱で接続する。 -/
def cosliceRetractionSectionComparison : SSet.Homotopy (a ≫ P') (a ≫ P) where
  h := (H).h ≫ P'
  h₀ := by
    change SSet.ι₀ ≫ ((H).h ≫ P') = a ≫ P'
    rw [← Category.assoc, (H).h₀]
  h₁ := by
    change SSet.ι₁ ≫ ((H).h ≫ P') = a ≫ P
    rw [← Category.assoc, (H).h₁,
      cosliceRetractionFamily_other_section d r s hs a s' hs']
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
        sliceUnderPostcomp d q = fst T Δ[1] ≫ (a ≫ P') ≫ sliceUnderPostcomp d q := by
  change ((H).h ≫ P') ≫ sliceUnderPostcomp d q = _
  rw [normalizedCoconeRestriction_postcomp_family,
    cosliceRetractionFamilyComparison_base]
  have h := congrArg (fun m ↦ fst T (Δ[1] : SSet.{u}) ≫ m)
    (normalizedCoconeRestriction_postcomp_family (r ≫ d) s' d
      (cosliceRetractionFamily_diagram d r s' hs') q a)
  simpa only [Category.assoc] using h.symm

/-- 二切断の比較も、元の可変終点の全族を全時刻保持する。 -/
lemma cosliceRetractionSectionComparison_projection :
    (cosliceRetractionSectionComparison d r s hs hsr q a b hb s' hs').h ≫
        sliceUnderProjection d = fst T Δ[1] ≫ a ≫ sliceUnderProjection (r ≫ d) := by
  rw [cosliceRetractionSectionComparison, Category.assoc,
    normalizedCoconeRestriction_projection, cosliceRetractionFamilyComparison_projection]

end
end SerrePositivity.InfinityCategories.HomotopyLimits
