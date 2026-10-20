module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CosliceRetractionFamily
public import SerrePositivity.InfinityCategories.HomotopyLimits.RelativeCosliceFamilyHomotopy

/-!
概要：収縮に沿う定値な底を持つ全余錐族を、切断から戻した族と相対的に比較する。
方針：切断と底の厳密な一致を、相対 coslice 制限の自明 Kan 性へ入力する。
規約：底と可変終点は全時刻固定。使われ方：定値な時間図式の二端の初期 Hom 比較。
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
include hsr hb

/-- 切断と底を保ち、元の全族を収縮による族へ結ぶ実際の比較が存在する。 -/
lemma exists_cosliceRetractionFamilyComparison :
    ∃ H : SSet.Homotopy a (cosliceRetractionFamily d r s hs a),
      H.h ≫ sliceUnderRestrict (r ≫ d) s =
        fst T Δ[1] ≫ a ≫ sliceUnderRestrict (r ≫ d) s ∧
      H.h ≫ sliceUnderPostcomp (r ≫ d) q =
        fst T Δ[1] ≫ a ≫ sliceUnderPostcomp (r ≫ d) q := by
  obtain ⟨H, hH, hq⟩ := exists_relativeCosliceFamilyHomotopy (r ≫ d) q s hsr a
    (cosliceRetractionFamily d r s hs a)
    (cosliceRetractionFamily_boundary d r s hs a).symm
    (cosliceRetractionFamily_base d r s hs a q b hb).symm
  refine ⟨H, ?_, ?_⟩
  · simpa only [cosliceRetractionFamily_boundary] using hH
  · simpa only [cosliceRetractionFamily_base d r s hs a q b hb] using hq

/-- 保持した切断と底の全族の上で定値な、同じ収縮族への比較円柱。 -/
def cosliceRetractionFamilyComparison :
    SSet.Homotopy a (cosliceRetractionFamily d r s hs a) :=
  (exists_cosliceRetractionFamilyComparison d r s hs hsr q a b hb).choose

/-- 比較は指定した切断上の全係数を全時刻固定する。 -/
lemma cosliceRetractionFamilyComparison_boundary :
    (cosliceRetractionFamilyComparison d r s hs hsr q a b hb).h ≫
        sliceUnderRestrict (r ≫ d) s = fst T Δ[1] ≫ a ≫ sliceUnderRestrict (r ≫ d) s :=
  (exists_cosliceRetractionFamilyComparison d r s hs hsr q a b hb).choose_spec.1

/-- 比較は底の全族を全時刻固定する。 -/
lemma cosliceRetractionFamilyComparison_base :
    (cosliceRetractionFamilyComparison d r s hs hsr q a b hb).h ≫
        sliceUnderPostcomp (r ≫ d) q = fst T Δ[1] ≫ a ≫ sliceUnderPostcomp (r ≫ d) q :=
  (exists_cosliceRetractionFamilyComparison d r s hs hsr q a b hb).choose_spec.2

/-- 同じ比較は可変終点の全族も全時刻で保持する。 -/
lemma cosliceRetractionFamilyComparison_projection :
    (cosliceRetractionFamilyComparison d r s hs hsr q a b hb).h ≫
        sliceUnderProjection (r ≫ d) = fst T Δ[1] ≫ a ≫ sliceUnderProjection (r ≫ d) := by
  have h := congrArg (fun m ↦ m ≫ sliceUnderProjection (s ≫ (r ≫ d)))
    (cosliceRetractionFamilyComparison_boundary d r s hs hsr q a b hb)
  simpa only [Category.assoc, sliceUnderRestrict_projection] using h

end
end SerrePositivity.InfinityCategories.HomotopyLimits
