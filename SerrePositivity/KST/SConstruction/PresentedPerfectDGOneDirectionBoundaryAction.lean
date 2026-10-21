module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGAssemblyAction
public import SerrePositivity.KST.SConstruction.OneDirectionBoundary

/-! # 一次方向の全零境界を保つ全 native dg 作用
概要：一次方向を固定した全作用は、残りの各零方向の像とその合併を保つ。
方針：零段からの包含の全パラメータ自然性で、像の元の原像を明示する。
規約：入力を通常射に制限しない。使われ方：元の suspension 構造写像への降下。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 一次方向を固定した全作用も、元の同じ多次数の全 core 作用で評価できる。 -/
lemma presentedPerfectDGOneDirectionAction_app (r : ℕ) (C D : PerfDGInput.{u, v} A)
    (n : SimplexCategoryᵒᵖ)
    (x : ((oneDirectionRealizationFunctor r).obj
      (stableCategoryModel (presentedPerfectDGStableCategory A C))).obj n)
    (p : (C ⟶[SSet.{max (u + 1) v}] D).obj n) :
    (presentedPerfectDGOneDirectionAction A r C D).app n (x, p) =
      (uncurry (((presentedPerfectDGMultiSCoreEnrichedDiagram A (r + 1)).obj
        ((oneDirectionIndex r).obj (fun _ => n))).map C D)).app n (x, p) :=
  coordinateEnrichedDiagonalAction_app
    (presentedPerfectDGMultiSCoreEnrichedDiagram A (r + 1))
    (multiIndexDiagonal r ⋙ oneDirectionIndex r) C D n x p

/-- 各零方向の元の像は、全 native 入力単体で保存される。 -/
lemma presentedPerfectDGOneDirectionAction_mem_zeroRange (r : ℕ) (j : Fin r)
    (C D : PerfDGInput.{u, v} A) (n : SimplexCategoryᵒᵖ)
    (x : ((oneDirectionRealizationFunctor r).obj
      (stableCategoryModel (presentedPerfectDGStableCategory A C))).obj n)
    (p : (C ⟶[SSet.{max (u + 1) v}] D).obj n)
    (hx : x ∈ (oneDirectionZeroRange r j
      (stableCategoryModel (presentedPerfectDGStableCategory A C))).obj n) :
    (presentedPerfectDGOneDirectionAction A r C D).app n (x, p) ∈
      (oneDirectionZeroRange r j
        (stableCategoryModel (presentedPerfectDGStableCategory A D))).obj n := by
  obtain ⟨y, rfl⟩ := hx
  let θ := (oneDirectionIndex r).map ((zeroDirectionsIndexNat {j}).app (fun _ => n))
  let E := presentedPerfectDGMultiSCoreEnrichedDiagram A (r + 1)
  have h := congrArg (fun q => q.app n (y, p)) ((E.map θ).property C D)
  refine ⟨(uncurry ((E.obj _).map C D)).app n (y, p), ?_⟩
  exact h.symm.trans
    (presentedPerfectDGOneDirectionAction_app A r C D n
      ((oneDirectionZeroInclusion r j
        (stableCategoryModel (presentedPerfectDGStableCategory A C))).app n y) p).symm

/-- 残りの全零境界の元の合併は、全 native 入力単体で保存される。 -/
lemma presentedPerfectDGOneDirectionAction_mem_fatBoundary (r : ℕ)
    (C D : PerfDGInput.{u, v} A) (n : SimplexCategoryᵒᵖ)
    (x : ((oneDirectionRealizationFunctor r).obj
      (stableCategoryModel (presentedPerfectDGStableCategory A C))).obj n)
    (p : (C ⟶[SSet.{max (u + 1) v}] D).obj n)
    (hx : x ∈ (oneDirectionFatBoundary r
      (stableCategoryModel (presentedPerfectDGStableCategory A C))).obj n) :
    (presentedPerfectDGOneDirectionAction A r C D).app n (x, p) ∈
      (oneDirectionFatBoundary r
        (stableCategoryModel (presentedPerfectDGStableCategory A D))).obj n := by
  simp only [oneDirectionFatBoundary, Subfunctor.iSup_obj, Set.mem_iUnion] at hx ⊢
  obtain ⟨j, hj⟩ := hx
  exact ⟨j, presentedPerfectDGOneDirectionAction_mem_zeroRange A r j C D n x p hj⟩

/-- 元の一次方向の全零境界への全パラメータ制限作用。 -/
def presentedPerfectDGOneDirectionBoundaryAction (r : ℕ) (C D : PerfDGInput.{u, v} A) :
    (oneDirectionFatBoundary r
      (stableCategoryModel (presentedPerfectDGStableCategory A C)) : SSet.{max (u + 1) v}) ⊗
        (C ⟶[SSet.{max (u + 1) v}] D) ⟶
    (oneDirectionFatBoundary r
      (stableCategoryModel (presentedPerfectDGStableCategory A D)) : SSet.{max (u + 1) v}) :=
  Subcomplex.lift
    (((oneDirectionFatBoundary r
      (stableCategoryModel (presentedPerfectDGStableCategory A C))).ι ⊗ₘ 𝟙 _) ≫
        presentedPerfectDGOneDirectionAction A r C D) (by
    intro n y hy
    obtain ⟨p, rfl⟩ := hy
    exact presentedPerfectDGOneDirectionAction_mem_fatBoundary A r C D n
      p.1.val p.2 p.1.property)

/-- 境界の包含後には、元の一次方向の全作用を厳密に回収する。 -/
lemma presentedPerfectDGOneDirectionBoundaryAction_inclusion (r : ℕ)
    (C D : PerfDGInput.{u, v} A) :
    presentedPerfectDGOneDirectionBoundaryAction A r C D ≫
      (oneDirectionFatBoundary r
        (stableCategoryModel (presentedPerfectDGStableCategory A D))).ι =
    ((oneDirectionFatBoundary r
      (stableCategoryModel (presentedPerfectDGStableCategory A C))).ι ⊗ₘ 𝟙 _) ≫
      presentedPerfectDGOneDirectionAction A r C D := Subcomplex.lift_ι _ _

end SerrePositivity.KST.SConstruction
