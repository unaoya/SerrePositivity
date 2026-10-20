module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedHomotopyLift
public import SerrePositivity.InfinityCategories.HomotopyLimits.RelativeRightCosliceSection

/-!
概要：終端係数が一致する二族の間に、指定した底の全ホモトピーを持ち上げる。
方針：定値な上の境界と指定した底を引き戻しへ束ね、自明 Kan 射に両端固定で持ち上げる。
規約：上の終端は全時刻固定し、底は指定円柱そのもの。使われ方：右長辺族の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 指定された底のホモトピーを、上の終端係数と両端の族を保って持ち上げる。 -/
lemma exists_relativeCosliceSpecifiedHomotopy {K J E B T : SSet.{u}}
    (t : K ⟶ E) (q : E ⟶ B) [InnerFibration q]
    (j : J ⟶ K) [Mono j] (hj : rightAnodyneExtensions j)
    (a b : T ⟶ sliceUnder t)
    (hab : a ≫ sliceUnderRestrict t j = b ≫ sliceUnderRestrict t j)
    (H : SSet.Homotopy (a ≫ sliceUnderPostcomp t q) (b ≫ sliceUnderPostcomp t q))
    (hH : H.h ≫ sliceUnderRestrict (t ≫ q) j =
      fst T Δ[1] ≫ b ≫ sliceUnderRestrict t j ≫ sliceUnderPostcomp (j ≫ t) q) :
    ∃ L : SSet.Homotopy a b,
      L.h ≫ sliceUnderRestrict t j = fst T Δ[1] ≫ b ≫ sliceUnderRestrict t j ∧
      L.h ≫ sliceUnderPostcomp t q = H.h := by
  have := relativeCosliceRestriction_of_rightAnodyne t q j hj
  let α := fst T (Δ[1] : SSet.{u}) ≫ b ≫ sliceUnderRestrict t j
  have hα : α ≫ sliceUnderPostcomp (j ≫ t) q =
      H.h ≫ sliceUnderRestrict (t ≫ q) j := by
    simpa only [α, Category.assoc] using hH.symm
  let P : SSet.Homotopy
      (a ≫ relativeCosliceRestriction t q j) (b ≫ relativeCosliceRestriction t q j) :=
    { h := pullback.lift α H.h hα
      h₀ := by
        change SSet.ι₀ ≫ pullback.lift α H.h hα = a ≫ relativeCosliceRestriction t q j
        apply pullback.hom_ext
        · simp only [relativeCosliceRestriction, squareComparison,
            Category.assoc, pullback.lift_fst]
          simp only [α, ← Category.assoc, SSet.ι₀_fst, Category.id_comp, hab]
        · simp only [relativeCosliceRestriction, squareComparison,
            Category.assoc, pullback.lift_snd]
          exact H.h₀
      h₁ := by
        change SSet.ι₁ ≫ pullback.lift α H.h hα = b ≫ relativeCosliceRestriction t q j
        apply pullback.hom_ext
        · simp only [relativeCosliceRestriction, squareComparison,
            Category.assoc, pullback.lift_fst]
          simp only [α, ← Category.assoc, SSet.ι₁_fst, Category.id_comp]
        · simp only [relativeCosliceRestriction, squareComparison,
            Category.assoc, pullback.lift_snd]
          exact H.h₁
      rel := by
        apply SSet.hom_ext
        intro n
        apply ConcreteCategory.hom_ext
        intro x
        exact False.elim x.1.property }
  obtain ⟨L, hL⟩ := exists_specifiedHomotopyLift (relativeCosliceRestriction t q j) a b P
  refine ⟨L, ?_, ?_⟩
  · have h := congrArg (fun k ↦ k ≫ pullback.fst _ _) hL
    simpa only [P, α, relativeCosliceRestriction, squareComparison, Category.assoc,
      pullback.lift_fst] using h
  · have h := congrArg (fun k ↦ k ≫ pullback.snd _ _) hL
    simpa only [P, relativeCosliceRestriction, squareComparison, Category.assoc,
      pullback.lift_snd] using h

end SerrePositivity.InfinityCategories.HomotopyLimits
