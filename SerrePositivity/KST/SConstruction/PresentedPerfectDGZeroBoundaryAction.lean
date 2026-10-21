module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGMultiRealizationAction
public import SerrePositivity.KST.SConstruction.BoundaryReduction

/-! # 元の全零境界を保つ全 native dg 作用
概要：元の反復実現の全パラメータ作用は、任意の零方向の像と全零境界を保存する。
方針：元の全多単体自然性を零方向の自己射へ適用し、固定点条件と有限合併を使う。
規約：選んだ零対象の厳密保存は要求しない。使われ方：同じ点つき商への全作用の降下。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 元の全 native 作用は、任意の零方向の元の冪等作用と厳密に可換。 -/
lemma presentedPerfectDGMultiRealizationAction_zeroOperator (r : ℕ)
    (s : Finset (Fin r)) (C D : PerfDGInput.{u, v} A) (n : SimplexCategoryᵒᵖ)
    (x : ((presentedPerfectDGMultiRealizationEnrichedFunctor A r).obj C).obj.obj n)
    (p : (C ⟶[SSet.{max (u + 1) v}] D).obj n) :
    (presentedPerfectDGMultiRealizationAction A r C D).app n
      (zeroDirectionsOperator s (stableCategoryModel (presentedPerfectDGStableCategory A C)) n x,
        p) =
      zeroDirectionsOperator s (stableCategoryModel (presentedPerfectDGStableCategory A D)) n
        ((presentedPerfectDGMultiRealizationAction A r C D).app n (x, p)) := by
  have h := ((presentedPerfectDGMultiSCoreEnrichedDiagram A r).map
    (zeroDirectionsIndexEndomorphism s (fun _ => n))).property C D
  let θ := zeroDirectionsIndexEndomorphism s (fun _ => n)
  let f := (multiCoreSConstruction r
    (stableCategoryModel (presentedPerfectDGStableCategory A C))).map θ
  let g := (multiCoreSConstruction r
    (stableCategoryModel (presentedPerfectDGStableCategory A D))).map θ
  let a := uncurry (((presentedPerfectDGMultiSCoreEnrichedDiagram A r).obj
    (fun _ => n)).map C D)
  have h₀ : a.app n (f.app n x, p) = g.app n (a.app n (x, p)) :=
    congrArg (fun q => q.app n (x, p)) h
  have hx := zeroDirectionsOperator_eq_map s
    (stableCategoryModel (presentedPerfectDGStableCategory A C)) n x
  have hy := zeroDirectionsOperator_eq_map s
    (stableCategoryModel (presentedPerfectDGStableCategory A D)) n
      ((presentedPerfectDGMultiRealizationAction A r C D).app n (x, p))
  exact (congrArg
    (fun y => (presentedPerfectDGMultiRealizationAction A r C D).app n (y, p)) hx).trans
      ((presentedPerfectDGMultiRealizationAction_app A r C D n (f.app n x) p).trans
        (h₀.trans ((congrArg (fun y => g.app n y)
          (presentedPerfectDGMultiRealizationAction_app A r C D n x p).symm).trans hy.symm)))

/-- 零方向の像の固定点条件は、全 native 入力単体で保存される。 -/
lemma presentedPerfectDGMultiRealizationAction_mem_zeroRange (r : ℕ)
    (s : Finset (Fin r)) (C D : PerfDGInput.{u, v} A) (n : SimplexCategoryᵒᵖ)
    (x : ((presentedPerfectDGMultiRealizationEnrichedFunctor A r).obj C).obj.obj n)
    (p : (C ⟶[SSet.{max (u + 1) v}] D).obj n)
    (hx : x ∈ (zeroDirectionsRange s
      (stableCategoryModel (presentedPerfectDGStableCategory A C))).obj n) :
    (presentedPerfectDGMultiRealizationAction A r C D).app n (x, p) ∈
      (zeroDirectionsRange s
        (stableCategoryModel (presentedPerfectDGStableCategory A D))).obj n := by
  apply (mem_zeroDirectionsRange_iff s _ n _).2
  exact (presentedPerfectDGMultiRealizationAction_zeroOperator A r s C D n x p).symm.trans
    (congrArg (fun y => (presentedPerfectDGMultiRealizationAction A r C D).app n (y, p))
      ((mem_zeroDirectionsRange_iff s _ n x).1 hx))

/-- 零方向の像の任意の有限合併は、全 native 入力単体で保存される。 -/
lemma presentedPerfectDGMultiRealizationAction_mem_zeroBoundary (r : ℕ)
    (s t : Finset (Fin r)) (C D : PerfDGInput.{u, v} A) (n : SimplexCategoryᵒᵖ)
    (x : ((presentedPerfectDGMultiRealizationEnrichedFunctor A r).obj C).obj.obj n)
    (p : (C ⟶[SSet.{max (u + 1) v}] D).obj n)
    (hx : x ∈ (zeroDirectionsBoundary s t
      (stableCategoryModel (presentedPerfectDGStableCategory A C))).obj n) :
    (presentedPerfectDGMultiRealizationAction A r C D).app n (x, p) ∈
      (zeroDirectionsBoundary s t
        (stableCategoryModel (presentedPerfectDGStableCategory A D))).obj n := by
  induction s using Finset.induction_on with
  | empty => exact False.elim hx
  | @insert i s _hi ih =>
    rw [zeroDirectionsBoundary_insert] at hx ⊢
    rcases hx with hx | hx
    · exact Or.inl (presentedPerfectDGMultiRealizationAction_mem_zeroRange A r _ C D n x p hx)
    · exact Or.inr (ih hx)

/-- 元の全零境界上の、全 native Kan dg 入力族による実作用。 -/
def presentedPerfectDGZeroBoundaryAction (r : ℕ) (C D : PerfDGInput.{u, v} A) :
    (zeroDirectionsFatBoundary r
      (stableCategoryModel (presentedPerfectDGStableCategory A C)) : SSet.{max (u + 1) v}) ⊗
        (C ⟶[SSet.{max (u + 1) v}] D) ⟶
      (zeroDirectionsFatBoundary r
        (stableCategoryModel (presentedPerfectDGStableCategory A D)) : SSet.{max (u + 1) v}) :=
  Subcomplex.lift
    (((zeroDirectionsFatBoundary r
      (stableCategoryModel (presentedPerfectDGStableCategory A C))).ι ⊗ₘ 𝟙 _) ≫
        presentedPerfectDGMultiRealizationAction A r C D) (by
    intro n y hy
    obtain ⟨p, rfl⟩ := hy
    exact presentedPerfectDGMultiRealizationAction_mem_zeroBoundary A r Finset.univ ∅
      C D n p.1.val p.2 p.1.property)

/-- 元の全零境界の包含後には、同じ全 native 実現作用を厳密に回収する。 -/
lemma presentedPerfectDGZeroBoundaryAction_inclusion (r : ℕ) (C D : PerfDGInput.{u, v} A) :
    presentedPerfectDGZeroBoundaryAction A r C D ≫
      (zeroDirectionsFatBoundary r
        (stableCategoryModel (presentedPerfectDGStableCategory A D))).ι =
      ((zeroDirectionsFatBoundary r
        (stableCategoryModel (presentedPerfectDGStableCategory A C))).ι ⊗ₘ 𝟙 _) ≫
          presentedPerfectDGMultiRealizationAction A r C D := Subcomplex.lift_ι _ _

end SerrePositivity.KST.SConstruction
