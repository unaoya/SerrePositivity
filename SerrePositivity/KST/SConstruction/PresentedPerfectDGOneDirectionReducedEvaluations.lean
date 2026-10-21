module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGOneDirectionReducedAction
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGOneDirectionActionLaws

/-! # 元の一次方向商の全作用法則の二脚評価
概要：合成と通常射の回収を、元の商射と基点の各入力単体上で証明する。
方針：既存の厳密回収式と降下前の全作用法則を同じ各次数で合成する。
規約：全次数・全入力族を保持する。使われ方：元の商の標準点つき豊穣化。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 元の厳密 dg 射が与える、同じ元の一次方向の点つき商射。 -/
def presentedPerfectDGOneDirectionPointedMap (r : ℕ)
    {C D : PerfDGInput.{u, v} A} (F : C ⟶ D) :
    oneDirectionReducedRealization r
      (stableCategoryModel (presentedPerfectDGStableCategory A C)) ⟶
    oneDirectionReducedRealization r
      (stableCategoryModel (presentedPerfectDGStableCategory A D)) :=
  oneDirectionReducedRealizationMap r
    ⟨(presentedPerfectDGExactMap A F).hom,
      preservesCofiberData_of_isExactFunctor (presentedPerfectDGExactMap A F).hom⟩

/-- 元の商射の像では、二回の商作用は同じ native 合成の作用と一致する。 -/
lemma presentedPerfectDGOneDirectionReducedAction_comp_quotient_app (r : ℕ)
    (C D E : PerfDGInput.{u, v} A) (n : SimplexCategoryᵒᵖ)
    (x : ((oneDirectionRealizationFunctor (r + 1)).obj
      (stableCategoryModel (presentedPerfectDGStableCategory A C))).obj n)
    (p : (C ⟶[SSet.{max (u + 1) v}] D).obj n)
    (q : (D ⟶[SSet.{max (u + 1) v}] E).obj n) :
    (presentedPerfectDGOneDirectionReducedAction A r D E).app n
      ((presentedPerfectDGOneDirectionReducedAction A r C D).app n
        ((oneDirectionReductionQuotient r
          (stableCategoryModel (presentedPerfectDGStableCategory A C))).app n x, p), q) =
    (presentedPerfectDGOneDirectionReducedAction A r C E).app n
      ((oneDirectionReductionQuotient r
        (stableCategoryModel (presentedPerfectDGStableCategory A C))).app n x,
        (eComp SSet.{max (u + 1) v} C D E).app n (p, q)) := by
  have h₁ := types_congr_hom (NatTrans.congr_app
    (presentedPerfectDGOneDirectionReducedAction_quotient A r C D) n) (x, p)
  have h₂ := types_congr_hom (NatTrans.congr_app
    (presentedPerfectDGOneDirectionReducedAction_quotient A r D E) n)
    ((presentedPerfectDGOneDirectionAction A (r + 1) C D).app n (x, p), q)
  have h₃ := types_congr_hom (NatTrans.congr_app
    (presentedPerfectDGOneDirectionReducedAction_quotient A r C E) n)
    (x, (eComp SSet.{max (u + 1) v} C D E).app n (p, q))
  have hh := types_congr_hom (NatTrans.congr_app
    (presentedPerfectDGOneDirectionAction_comp A (r + 1) C D E) n) ((x, p), q)
  exact (congrArg (fun y => (presentedPerfectDGOneDirectionReducedAction A r D E).app n
    (y, q)) h₁).trans (h₂.trans ((congrArg (fun y => (oneDirectionReductionQuotient r
      (stableCategoryModel (presentedPerfectDGStableCategory A E))).app n y) hh).trans h₃.symm))

/-- 元の基点上でも、二回の商作用は同じ native 合成の作用と一致する。 -/
lemma presentedPerfectDGOneDirectionReducedAction_comp_basepoint_app (r : ℕ)
    (C D E : PerfDGInput.{u, v} A) (n : SimplexCategoryᵒᵖ)
    (t : (𝟙_ SSet.{max (u + 1) v}).obj n)
    (p : (C ⟶[SSet.{max (u + 1) v}] D).obj n)
    (q : (D ⟶[SSet.{max (u + 1) v}] E).obj n) :
    (presentedPerfectDGOneDirectionReducedAction A r D E).app n
      ((presentedPerfectDGOneDirectionReducedAction A r C D).app n
        ((oneDirectionReducedRealization r
          (stableCategoryModel (presentedPerfectDGStableCategory A C))).hom.app n t, p), q) =
    (presentedPerfectDGOneDirectionReducedAction A r C E).app n
      ((oneDirectionReducedRealization r
        (stableCategoryModel (presentedPerfectDGStableCategory A C))).hom.app n t,
        (eComp SSet.{max (u + 1) v} C D E).app n (p, q)) := by
  have h₁ := types_congr_hom (NatTrans.congr_app
    (presentedPerfectDGOneDirectionReducedAction_basepoint A r C D) n) (t, p)
  have h₂ := types_congr_hom (NatTrans.congr_app
    (presentedPerfectDGOneDirectionReducedAction_basepoint A r D E) n)
    ((CartesianMonoidalCategory.toUnit ((𝟙_ SSet.{max (u + 1) v}) ⊗
      (C ⟶[SSet.{max (u + 1) v}] D))).app n (t, p), q)
  have h₃ := types_congr_hom (NatTrans.congr_app
    (presentedPerfectDGOneDirectionReducedAction_basepoint A r C E) n)
    (t, (eComp SSet.{max (u + 1) v} C D E).app n (p, q))
  exact (congrArg (fun y => (presentedPerfectDGOneDirectionReducedAction A r D E).app n
    (y, q)) h₁).trans (h₂.trans h₃.symm)

/-- 元の商射の像では、通常 dg 射を同じ元の点つき商射として回収する。 -/
lemma presentedPerfectDGOneDirectionReducedAction_hom_quotient_app (r : ℕ)
    {C D : PerfDGInput.{u, v} A} (F : C ⟶ D) (n : SimplexCategoryᵒᵖ)
    (x : ((oneDirectionRealizationFunctor (r + 1)).obj
      (stableCategoryModel (presentedPerfectDGStableCategory A C))).obj n)
    (t : (𝟙_ SSet.{max (u + 1) v}).obj n) :
    (presentedPerfectDGOneDirectionReducedAction A r C D).app n
      ((oneDirectionReductionQuotient r
        (stableCategoryModel (presentedPerfectDGStableCategory A C))).app n x,
        (eHomEquiv SSet.{max (u + 1) v} F).app n t) =
    (presentedPerfectDGOneDirectionPointedMap A r F).right.app n
      ((oneDirectionReductionQuotient r
        (stableCategoryModel (presentedPerfectDGStableCategory A C))).app n x) := by
  have hd := types_congr_hom (NatTrans.congr_app
    (presentedPerfectDGOneDirectionReducedAction_quotient A r C D) n)
    (x, (eHomEquiv SSet.{max (u + 1) v} F).app n t)
  have hh := types_congr_hom (NatTrans.congr_app
    (presentedPerfectDGOneDirectionAction_hom A (r + 1) F) n) (x, t)
  have hq := types_congr_hom (NatTrans.congr_app
    (oneDirectionReducedRealizationMap_quotient r
      (show stableCategoryModel (presentedPerfectDGStableCategory A C) ⟶
        stableCategoryModel (presentedPerfectDGStableCategory A D) from
        ⟨(presentedPerfectDGExactMap A F).hom,
          preservesCofiberData_of_isExactFunctor (presentedPerfectDGExactMap A F).hom⟩)) n) x
  exact hd.trans ((congrArg (fun y => (oneDirectionReductionQuotient r
    (stableCategoryModel (presentedPerfectDGStableCategory A D))).app n y) hh).trans hq.symm)

/-- 基点上でも、通常 dg 射を同じ元の点つき商射として回収する。 -/
lemma presentedPerfectDGOneDirectionReducedAction_hom_basepoint_app (r : ℕ)
    {C D : PerfDGInput.{u, v} A} (F : C ⟶ D) (n : SimplexCategoryᵒᵖ)
    (t t' : (𝟙_ SSet.{max (u + 1) v}).obj n) :
    (presentedPerfectDGOneDirectionReducedAction A r C D).app n
      ((oneDirectionReducedRealization r
        (stableCategoryModel (presentedPerfectDGStableCategory A C))).hom.app n t,
        (eHomEquiv SSet.{max (u + 1) v} F).app n t') =
    (presentedPerfectDGOneDirectionPointedMap A r F).right.app n
      ((oneDirectionReducedRealization r
        (stableCategoryModel (presentedPerfectDGStableCategory A C))).hom.app n t) := by
  have : Subsingleton ((𝟙_ SSet.{max (u + 1) v}).obj n) := by
    change Subsingleton PUnit
    infer_instance
  have hd := types_congr_hom (NatTrans.congr_app
    (presentedPerfectDGOneDirectionReducedAction_basepoint A r C D) n)
    (t, (eHomEquiv SSet.{max (u + 1) v} F).app n t')
  have hw := types_congr_hom (NatTrans.congr_app
    (Under.w (presentedPerfectDGOneDirectionPointedMap A r F)) n) t
  exact hd.trans ((congrArg (fun x => (oneDirectionReducedRealization r
    (stableCategoryModel (presentedPerfectDGStableCategory A D))).hom.app n x)
      (Subsingleton.elim _ _)).trans hw.symm)

end SerrePositivity.KST.SConstruction
