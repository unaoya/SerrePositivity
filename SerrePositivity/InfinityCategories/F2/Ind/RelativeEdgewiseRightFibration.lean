module

public import SerrePositivity.InfinityCategories.F2.Ind.RelativeEdgewiseRightComparison
public import SerrePositivity.InfinityCategories.F2.Ind.EdgewiseRelativeBoundaryExtension

/-!
概要：right fibration の twisted arrow の相対右端比較は自明 Kan fibration。
方針：零次元は終点包含、正次元は右半分と全境界面を保つ相対重みの延長で解く。
規約：元の比較写像自身の全境界充填を証明し、各点の同値で代用しない。
使われ方：元の圏の全高次に整合する Yoneda 密度の比較族を選ぶ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {E B : SSet.{u}} (p : E ⟶ B) [RightFibration p]

/-- 元の相対右端比較の零次元の境界は、指定された同じ終点から持ち上がる。 -/
lemma relativeEdgewiseRightComparison_boundary_zero :
    HasLiftingProperty (boundary.{u} 0).ι (relativeEdgewiseRightComparison p) := by
  constructor
  intro a b sq
  let g := SSet.yonedaEquiv (b ≫ pullback.fst (edgewiseRight B) p)
  let e := b ≫ pullback.snd (edgewiseRight B) p
  have he : e ≫ p = joinInr (Δ[0] : SSet.{u}).op Δ[0] ≫ g := by
    rw [edgewiseRight_yoneda]
    dsimp only [e]
    rw [Category.assoc, ← pullback.condition, ← Category.assoc]
  have := edgewiseWeight_zero_inr_rightAnodyne p (RightFibration.mem (p := p))
  let s : CommSq e (joinInr (Δ[0] : SSet.{u}).op Δ[0]) p g := ⟨he⟩
  exact CommSq.HasLift.mk'
    { l := SSet.yonedaEquiv.symm s.lift
      fac_left := boundary.hom_ext₀
      fac_right := relativeEdgewiseRightComparison_filler p b s.lift s.fac_right s.fac_left }

/-- 正次元の境界も、同じ元の射影と右半分を同時に保って持ち上がる。 -/
lemma relativeEdgewiseRightComparison_boundary_succ (n : ℕ) :
    HasLiftingProperty (boundary.{u} (n + 1)).ι (relativeEdgewiseRightComparison p) := by
  constructor
  intro a b sq
  have hmap : a ≫ edgewiseSubdivisionMap p =
      (boundary (n + 1)).ι ≫ (b ≫ pullback.fst _ _) := by
    have h := congrArg (fun f ↦ f ≫ pullback.fst (edgewiseRight B) p) sq.w
    simpa only [Category.assoc, relativeEdgewiseRightComparison_fst] using h
  have hright : CommSq a (boundary (n + 1)).ι (edgewiseRight E)
      (b ≫ pullback.snd (edgewiseRight B) p) := by
    constructor
    have h := congrArg (fun f ↦ f ≫ pullback.snd (edgewiseRight B) p) sq.w
    simpa only [Category.assoc, relativeEdgewiseRightComparison_snd] using h
  have he : (b ≫ pullback.snd _ _) ≫ p =
      joinInr (Δ[n + 1] : SSet.{u}).op Δ[n + 1] ≫
        SSet.yonedaEquiv (b ≫ pullback.fst _ _) := by
    rw [edgewiseRight_yoneda, Category.assoc, ← pullback.condition, ← Category.assoc]
  have hf (i : Fin (n + 2)) : SSet.yonedaEquiv (boundary.ι i ≫ a) ≫ p =
      edgewiseWeight.map (SimplexCategory.δ i) ≫
        SSet.yonedaEquiv (b ≫ pullback.fst _ _) := by
    calc
      _ = SSet.yonedaEquiv ((boundary.ι i ≫ a) ≫ edgewiseSubdivisionMap p) := rfl
      _ = SSet.yonedaEquiv (stdSimplex.δ i ≫ (b ≫ pullback.fst _ _)) := by
        rw [Category.assoc, hmap, ← Category.assoc, boundary.ι_ι]
      _ = _ := edgewiseSubdivision_yoneda_restriction _ _
  obtain ⟨F, hF, hR, hP⟩ := exists_edgewiseRight_relative_weight_extension p a
    (b ≫ pullback.snd _ _) hright (SSet.yonedaEquiv (b ≫ pullback.fst _ _)) he hf
  exact CommSq.HasLift.mk'
    { l := SSet.yonedaEquiv.symm F
      fac_left := edgewiseSubdivision_boundary_extension a F hF
      fac_right := relativeEdgewiseRightComparison_filler p b F hP hR }

/-- 同じ全族の相対 twisted arrow 比較は、追加仮定なしで自明 Kan fibration。 -/
instance relativeEdgewiseRightComparison_trivialKanFibration :
    TrivialKanFibration (relativeEdgewiseRightComparison p) := by
  apply (trivialKanFibration_iff_boundary _).2
  intro n
  cases n with
  | zero => exact relativeEdgewiseRightComparison_boundary_zero p
  | succ n => exact relativeEdgewiseRightComparison_boundary_succ p n

end SerrePositivity.InfinityCategories.F2.Ind
