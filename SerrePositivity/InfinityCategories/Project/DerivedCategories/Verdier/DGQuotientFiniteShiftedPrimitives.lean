module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGQuotientFiniteShiftedKernel
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGRepresentableDerivedPrimitives

/-! # 有限個のシフト次数の障害に対する共通実分母と実原始元

概要：シフト比較後に導来零となる有限個の閉加群射を、一つの実分母で境界にする。
方針：シフト交換同型で全次数の核の同時零化へ渡し、射影性で実 Hom end の原始元へ戻す。
規約：各整数シフトを固定する。使われ方：高次境界の各成分の具体的な相対零化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded DGQuotient SSet
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]

/-- 有限個の次数の比較の核から、共通実分母と全 Hom end の実原始元を構成する。 -/
theorem dgQuotientFiniteShifted_exists_primitives (P : Set D)
    (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P) {m : ℕ} (x : D) (y : Fin m → D) (n : Fin m → ℤ)
    (f : ∀ i, ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.representable A x) ⟶
      (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.representable A (y i)) : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D)⟦n i⟧)
    (hf : ∀ i, (_root_.SerrePositivity.DifferentialGraded.moduleToDerived A D).map (f i ≫
      (_root_.SerrePositivity.DifferentialGraded.representableRestrictionMap A D (_root_.SerrePositivity.DifferentialGraded.DGQuotient.QuotientObject D P) (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P) (y i))⟦n i⟧')
        = 0) :
    ∃ (q : D) (s : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex q) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)), s.edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P ∧
      ∀ i, ∃ h : (_root_.SerrePositivity.DifferentialGraded.moduleHom A D (_root_.SerrePositivity.DifferentialGraded.representable A q)
        (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A)
          ((ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.representable A (y i)) :
            _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D)⟦n i⟧))).X (-1),
        (_root_.SerrePositivity.DifferentialGraded.moduleHom A D (_root_.SerrePositivity.DifferentialGraded.representable A q)
          (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A)
            ((ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.representable A (y i)) :
              _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D)⟦n i⟧))).d (-1) 0 h =
          (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A (_root_.SerrePositivity.DifferentialGraded.RightModule A D) _ _
            ((dgYoneda A D).onClosed.map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed s) ≫ f i)).val := by
  let L := _root_.SerrePositivity.DifferentialGraded.moduleToDerived A D
  let a (i : Fin m) := L.map (f i) ≫ (L.commShiftIso (n i)).hom.app
    (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.representable A (y i)))
  have ha (i : Fin m) : a i ≫ (L.map
      (_root_.SerrePositivity.DifferentialGraded.representableRestrictionMap A D (_root_.SerrePositivity.DifferentialGraded.DGQuotient.QuotientObject D P) (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P) (y i)))⟦n i⟧'
        = 0 := by
    dsimp only [a]
    have hn := (L.commShiftIso (n i)).hom.naturality
      (_root_.SerrePositivity.DifferentialGraded.representableRestrictionMap A D (_root_.SerrePositivity.DifferentialGraded.DGQuotient.QuotientObject D P) (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P) (y i))
    simp only [Functor.comp_map] at hn
    rw [Category.assoc, ← hn,
      ← Category.assoc, ← L.map_comp, hf i, Limits.zero_comp]
  obtain ⟨q, s, hs, hz⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientFiniteShiftedKernel_exists_denominator A D P hP x y n a ha
  refine ⟨q, s, hs, fun i => (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveDerived_zero_iff_primitive A D
    (_root_.SerrePositivity.DifferentialGraded.representable_homotopicallyProjective A D q) _).mp ?_⟩
  apply (cancel_mono ((L.commShiftIso (n i)).hom.app
    (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.representable A (y i))))).mp
  rw [Limits.zero_comp, Functor.map_comp, Category.assoc]
  exact hz i

end SerrePositivity.InfinityCategories.Project.DerivedCategories
