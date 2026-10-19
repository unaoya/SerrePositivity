module
public import SerrePositivity.InfinityCategories.Derived.DGFiniteCellGradedPrimitives
public import SerrePositivity.InfinityCategories.Derived.DGFiniteVerdierDenominators
public import SerrePositivity.InfinityCategories.Derived.DGDerivedEdgeComposition

/-! # 有限 cell 加群標的の有限族を一つの元の実分母で同時に消す

概要：異なる標的・整数次数の閉元を、一つの閉 Verdier 分母の後で全て境界にする。
方針：有限個の導来零化分母を実共通分母で細分し、同じ閉射から原始元を回収する。
規約：空族も含む。使われ方：実有限図式の全辺の cone 残差の同時消去。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.HomotopyComparison SSet
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]

/-- 指定有限 cell 標的への導来射の有限族を、一つの元の実閉分母で同時に零化する。 -/
theorem dgFiniteCellTargets_exists_closedDenominator (P : Set D) {m : ℕ} (x : D)
    (Y : Fin m → DerivedModuleCategory A D) (hY : ∀ i, derivedFiniteCellOver A D P (Y i))
    (f : ∀ i, (moduleToDerived A D).obj
      (ForgetEnrichment.of (Complex A) (representable A x)) ⟶ Y i) :
    ∃ (q : D) (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) x),
      (dgClosedEdge A D s).edge ∈ dgVerdierEdges A D P ∧
        ∀ i, dgRepresentableDerivedMap A D s ≫ f i = 0 := by
  choose q s hs hz using fun i =>
    dgFiniteCellTarget_exists_closedDenominator A D P x (hY i) (f i)
  obtain ⟨q', t, ht, r, hr⟩ := dgVerdierEdges_commonDenominator A D P q
    (fun i => dgClosedEdge A D (s i)) hs
  refine ⟨q', edgeClosed t, ?_, fun i => ?_⟩
  · rw [dgClosedEdge_edgeClosed]
    exact ht
  · have hc := dgRepresentableDerivedEdgeMap_compStruct A D (hr i).2.some
    change dgRepresentableDerivedEdgeMap A D t ≫ f i = 0
    rw [← hc, Category.assoc]
    change dgRepresentableDerivedEdgeMap A D (r i) ≫
      dgRepresentableDerivedMap A D (edgeClosed (dgClosedEdge A D (s i))) ≫ f i = 0
    rw [dgClosedEdge_closed, hz i, Limits.comp_zero]

/-- 任意次数・有限 cell 標的の有限族は、一つの元の実閉分母の後で同時に境界になる。 -/
theorem dgFiniteCellGraded_exists_simultaneous_closedPrimitives (P : Set D) {m : ℕ} (x : D)
    (M : Fin m → ModuleCategory A D)
    (hM : ∀ i, derivedFiniteCellOver A D P ((moduleToDerived A D).obj (M i)))
    (n k : Fin m → ℤ) (hkn : ∀ i, k i + 1 = n i)
    (f : ∀ i, GradedHom A (representable A x) (ForgetEnrichment.to (Complex A) (M i)) (n i))
    (hf : ∀ i, differential A (f i) = 0) :
    ∃ (q : D) (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) x),
      (dgClosedEdge A D s).edge ∈ dgVerdierEdges A D P ∧
        ∀ i, ∃ h : GradedHom A (representable A q)
            (ForgetEnrichment.to (Complex A) (M i)) (k i),
          (moduleHom A D (representable A q) (ForgetEnrichment.to (Complex A) (M i))).d
            (k i) (n i) h = dgRepresentableModulePrecompose A D (n i) (f i) s := by
  let F := moduleToDerived A D
  let c i := dgModuleClosedRightShift A D (n i) (f i) (hf i)
  have hshift i : derivedFiniteCellOver A D P (F.obj ((M i)⟦n i⟧)) :=
    (derivedFiniteCellOver A D P).prop_of_iso ((F.commShiftIso (n i)).app (M i)).symm
      ((derivedFiniteCellOver A D P).le_shift (n i) _ (hM i))
  obtain ⟨q, s, hs, hz⟩ := dgFiniteCellTargets_exists_closedDenominator A D P x
    (fun i => F.obj ((M i)⟦n i⟧)) hshift (fun i => F.map (c i))
  let t := (dgYoneda A D).onClosed.map s
  refine ⟨q, s, hs, fun i => ?_⟩
  have hz' : F.map (t ≫ c i) = 0 := by
    rw [Functor.map_comp]
    exact hz i
  obtain ⟨b, hb⟩ := (dgModuleProjectiveDerived_zero_iff_primitive A D
    (representable_homotopicallyProjective A D q) (t ≫ c i)).mp hz'
  apply (dgModuleHomRightShift_exists_primitive_iff A D (n i) (k i) (hkn i)
    (dgRepresentableModulePrecompose A D (n i) (f i) s)).mp
  exact ⟨b, hb.trans (dgModuleClosedRightShift_precompose_cycle A D (n i) (f i) (hf i) t)⟩

end SerrePositivity.InfinityCategories
