module
public import SerrePositivity.KST.SConstruction.StableMultiRealizationAction
public import SerrePositivity.KST.SConstruction.BoundaryReduction

/-! # 元の全零境界を保つ完全関手の全作用
概要：元の反復実現の全パラメータ作用は、任意の零方向の像と全零境界を保存する。
方針：元の全多単体自然性を零方向の自己射へ適用し、固定点条件と有限合併を使う。
規約：選んだ零対象の厳密保存は要求しない。使われ方：同じ点つき商への全作用の降下。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories LocalizingInvariants

/-- 元の安定入力の全作用は、任意の零方向の元の冪等作用と厳密に可換。 -/
lemma stableMultiRealizationAction_zeroOperator (r : ℕ)
    (s : Finset (Fin r)) (C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) (n : SimplexCategoryᵒᵖ)
    (x : ((stableMultiRealizationEnrichedFunctor r).obj C).obj.obj n)
    (p : (C ⟶[SSet.{u}] D).obj n) :
    (stableMultiRealizationAction r C D).app n
      (zeroDirectionsOperator s (stableCategoryModel C) n x,
        p) =
      zeroDirectionsOperator s (stableCategoryModel D) n
        ((stableMultiRealizationAction r C D).app n (x, p)) := by
  have h := ((stableMultiSCoreEnrichedDiagram r).map
    (zeroDirectionsIndexEndomorphism s (fun _ => n))).property C D
  let θ := zeroDirectionsIndexEndomorphism s (fun _ => n)
  let f := (multiCoreSConstruction r
    (stableCategoryModel C)).map θ
  let g := (multiCoreSConstruction r
    (stableCategoryModel D)).map θ
  let a := uncurry (((stableMultiSCoreEnrichedDiagram r).obj
    (fun _ => n)).map C D)
  have h₀ : a.app n (f.app n x, p) = g.app n (a.app n (x, p)) :=
    congrArg (fun q => q.app n (x, p)) h
  have hx := zeroDirectionsOperator_eq_map s
    (stableCategoryModel C) n x
  have hy := zeroDirectionsOperator_eq_map s
    (stableCategoryModel D) n
      ((stableMultiRealizationAction r C D).app n (x, p))
  exact (congrArg
    (fun y => (stableMultiRealizationAction r C D).app n (y, p)) hx).trans
      ((stableMultiRealizationAction_app r C D n (f.app n x) p).trans
        (h₀.trans ((congrArg (fun y => g.app n y)
          (stableMultiRealizationAction_app r C D n x p).symm).trans hy.symm)))

/-- 零方向の像の固定点条件は、安定入力の全単体で保存される。 -/
lemma stableMultiRealizationAction_mem_zeroRange (r : ℕ)
    (s : Finset (Fin r)) (C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) (n : SimplexCategoryᵒᵖ)
    (x : ((stableMultiRealizationEnrichedFunctor r).obj C).obj.obj n)
    (p : (C ⟶[SSet.{u}] D).obj n)
    (hx : x ∈ (zeroDirectionsRange s
      (stableCategoryModel C)).obj n) :
    (stableMultiRealizationAction r C D).app n (x, p) ∈
      (zeroDirectionsRange s
        (stableCategoryModel D)).obj n := by
  apply (mem_zeroDirectionsRange_iff s _ n _).2
  exact (stableMultiRealizationAction_zeroOperator r s C D n x p).symm.trans
    (congrArg (fun y => (stableMultiRealizationAction r C D).app n (y, p))
      ((mem_zeroDirectionsRange_iff s _ n x).1 hx))

/-- 零方向の像の任意の有限合併は、安定入力の全単体で保存される。 -/
lemma stableMultiRealizationAction_mem_zeroBoundary (r : ℕ)
    (s t : Finset (Fin r)) (C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) (n : SimplexCategoryᵒᵖ)
    (x : ((stableMultiRealizationEnrichedFunctor r).obj C).obj.obj n)
    (p : (C ⟶[SSet.{u}] D).obj n)
    (hx : x ∈ (zeroDirectionsBoundary s t
      (stableCategoryModel C)).obj n) :
    (stableMultiRealizationAction r C D).app n (x, p) ∈
      (zeroDirectionsBoundary s t
        (stableCategoryModel D)).obj n := by
  induction s using Finset.induction_on with
  | empty => exact False.elim hx
  | @insert i s _hi ih =>
    rw [zeroDirectionsBoundary_insert] at hx ⊢
    rcases hx with hx | hx
    · exact Or.inl (stableMultiRealizationAction_mem_zeroRange r _ C D n x p hx)
    · exact Or.inr (ih hx)

/-- 元の全零境界上の、完全関手の全自然同値入力族による実作用。 -/
def stableZeroBoundaryAction (r : ℕ) (C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    (zeroDirectionsFatBoundary r
      (stableCategoryModel C) : SSet.{u}) ⊗
        (C ⟶[SSet.{u}] D) ⟶
      (zeroDirectionsFatBoundary r
        (stableCategoryModel D) : SSet.{u}) :=
  Subcomplex.lift
    (((zeroDirectionsFatBoundary r
      (stableCategoryModel C)).ι ⊗ₘ 𝟙 _) ≫
        stableMultiRealizationAction r C D) (by
    intro n y hy
    obtain ⟨p, rfl⟩ := hy
    exact stableMultiRealizationAction_mem_zeroBoundary r Finset.univ ∅
      C D n p.1.val p.2 p.1.property)

/-- 元の全零境界の包含後には、同じ安定入力の全実現作用を厳密に回収する。 -/
lemma stableZeroBoundaryAction_inclusion (r : ℕ) (C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    stableZeroBoundaryAction r C D ≫
      (zeroDirectionsFatBoundary r
        (stableCategoryModel D)).ι =
      ((zeroDirectionsFatBoundary r
        (stableCategoryModel C)).ι ⊗ₘ 𝟙 _) ≫
          stableMultiRealizationAction r C D := Subcomplex.lift_ι _ _

end SerrePositivity.KST.SConstruction
