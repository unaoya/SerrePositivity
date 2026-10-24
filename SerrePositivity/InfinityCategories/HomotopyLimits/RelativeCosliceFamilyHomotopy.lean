module

public import SerrePositivity.InfinityCategories.HomotopyLimits.RelativeRightCosliceSection
public import SerrePositivity.InfinityCategories.F1B.Fibrations.TrivialFibrationHomotopy

/-!
概要：同じ境界と底を持つ全余錐族を、両方を全時刻で保つ円柱で結ぶ。
方針：相対 coslice 制限の自明 Kan fibration へ相対ホモトピーの存在を適用する。
規約：全パラメータの境界と底の等式を要求する。使われ方：根辺円柱の端面の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 同じ境界と底の全族を持ち上げる二つの余錐族は、両方の上で定値に結べる。 -/
lemma exists_relativeCosliceFamilyHomotopy {K J E B T : SSet.{u}}
    (t : K ⟶ E) (q : E ⟶ B) [InnerFibration q]
    (j : J ⟶ K) [Mono j] (hj : rightAnodyneExtensions j)
    (a b : T ⟶ sliceUnder t)
    (hterminal : a ≫ sliceUnderRestrict t j = b ≫ sliceUnderRestrict t j)
    (hbase : a ≫ sliceUnderPostcomp t q = b ≫ sliceUnderPostcomp t q) :
    ∃ H : SSet.Homotopy a b,
      H.h ≫ sliceUnderRestrict t j =
        fst T (Δ[1] : SSet.{u}) ≫ b ≫ sliceUnderRestrict t j ∧
      H.h ≫ sliceUnderPostcomp t q =
        fst T (Δ[1] : SSet.{u}) ≫ b ≫ sliceUnderPostcomp t q := by
  have := relativeCosliceRestriction_of_rightAnodyne t q j hj
  have hab : a ≫ relativeCosliceRestriction t q j =
      b ≫ relativeCosliceRestriction t q j := by
    apply pullback.hom_ext
    · simpa only [relativeCosliceRestriction, squareComparison, Category.assoc,
        pullback.lift_fst] using hterminal
    · simpa only [relativeCosliceRestriction, squareComparison, Category.assoc,
        pullback.lift_snd] using hbase
  obtain ⟨H, hH⟩ := exists_homotopy_over_trivialKanFibration
    (relativeCosliceRestriction t q j) a b hab
  refine ⟨H, ?_, ?_⟩
  · have h := congrArg (fun k ↦ k ≫ pullback.fst _ _) hH
    simpa only [relativeCosliceRestriction, squareComparison, Category.assoc,
      pullback.lift_fst] using h
  · have h := congrArg (fun k ↦ k ≫ pullback.snd _ _) hH
    simpa only [relativeCosliceRestriction, squareComparison, Category.assoc,
      pullback.lift_snd] using h

end SerrePositivity.InfinityCategories.HomotopyLimits
