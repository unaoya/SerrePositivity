module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Triangles.DGYonedaClosedShiftSurjective
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGRestrictionLiftPrecomposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleShiftedComparisonBoundary
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleRightShiftPostcomposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGQuotientShiftedRoofs

/-! # 商の斉次閉元の元の実分母と斉次分子による分数表示

概要：商の任意次数の斉次閉元に、元の実分母・斉次閉分子・商の実比較境界を構成する。
方針：シフト閉加群 roof の分子を元へ戻し、導来比較式を斉次差の実原始元へ反映する。
規約：入力の商の斉次元を固定する。使われ方：β3 の指定高次境界の相対充填。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded DGQuotient
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]

/-- 商の斉次閉元は、元の実分母と斉次閉分子および商内の実原始元で分数表示できる。 -/
theorem dgQuotientGraded_exists_fraction (P : Set D) (hP : localKFlat A D P)
    (x y : D) (n : ℤ)
    (c : GradedHom A ((inclusion A D P).obj x) ((inclusion A D P).obj y) n)
    (hc : differential A c = 0) :
    ∃ (q : D) (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) x),
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P ∧
      ∃ a : GradedHom A q y n, differential A a = 0 ∧
        ∃ b : GradedHom A ((inclusion A D P).obj q) ((inclusion A D P).obj y) (n - 1),
          (homObject A (QuotientObject D P) ((inclusion A D P).obj q)
            ((inclusion A D P).obj y)).d (n - 1) n b =
              ((inclusion A D P).map q y).f n a -
                compose A c (((inclusion A D P).map q x).f 0
                  (closedHomEquiv A D _ _ s).val) (zero_add n) := by
  let F := inclusion A D P
  let L := moduleToDerived A D
  let R := restrictModule A D (QuotientObject D P) F.op (representable A (F.obj y))
  let N := (moduleRestriction A D (QuotientObject D P) F.op).obj
    (ForgetEnrichment.of (Complex A) (representable A (F.obj y)))
  let u := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRestrictionGradedLiftClosed A D (QuotientObject D P) F n c hc
  obtain ⟨q, s, g, hs, hr⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientShifted_exists_closedRoof A D P hP x y n
    (L.map u ≫ (L.commShiftIso n).hom.app N)
  obtain ⟨a, ha, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgYonedaClosedRightShift_surjective A D q y n g
  let t := (dgYoneda A D).onClosed.map s
  have hD : L.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgYonedaClosedRightShift A D n a ha ≫
      (representableRestrictionMap A D (QuotientObject D P) F y)⟦n⟧') = L.map (t ≫ u) := by
    apply (cancel_mono ((L.commShiftIso n).hom.app N)).mp
    have hn := (L.commShiftIso n).hom.naturality
      (representableRestrictionMap A D (QuotientObject D P) F y)
    simp only [Functor.comp_map] at hn
    simp only [Functor.map_comp, Category.assoc]
    rw [hn]
    simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableDerivedMap, Category.assoc] using hr
  let p : (moduleHom A D (representable A q) R).X n := (eHomWhiskerLeft (Complex A)
    (ForgetEnrichment.of (Complex A) (representable A q) : ModuleCategory A D)
    (representableRestrictionMap A D (QuotientObject D P) F y)).f n
      ((yonedaHom A D q y).f n a)
  let r : (moduleHom A D (representable A q) R).X n :=
    compose A (D := RightModule A D) (x := representable A q) (y := representable A x)
      (z := R)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRestrictionGradedLift A D (QuotientObject D P) F n c)
    (closedHomEquiv A (RightModule A D) _ _ t).val (zero_add n)
  have hp := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleClosedRightShift_postcompose_cycle A D n
    ((yonedaHom A D q y).f n a) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgYonedaGraded_closed A D n a ha)
    (representableRestrictionMap A D (QuotientObject D P) F y)
  have hr' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleClosedRightShift_precompose_cycle A D n
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRestrictionGradedLift A D (QuotientObject D P) F n c)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRestrictionGradedLift_closed A D (QuotientObject D P) F n c hc) t
  obtain ⟨b, hb⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleShiftedComparison_exists_primitive A D
    (representable_homotopicallyProjective A D q) n (n - 1) (by omega)
    _ _ p r hp hr' hD
  have hb' := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgComplexIso_exists_primitive_iff A
    (dgYonedaIso A q (restrictModule A D (QuotientObject D P) F.op
      (representable A (F.obj y)))).hom (n - 1) n (p - r)).mpr ⟨b, hb⟩
  have he := congrArg (fun f => f.f n a)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRestrictionGradedComparison_evaluation A D (QuotientObject D P) F q y)
  change (dgYonedaIso A q (restrictModule A D (QuotientObject D P) F.op
    (representable A (F.obj y)))).hom.f n p = (F.map q y).f n a at he
  have ht := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRestrictionGradedLift_precompose_evaluation A D (QuotientObject D P) F n c s
  obtain ⟨b', hb'⟩ := hb'
  refine ⟨q, s, hs, a, ha, b', ?_⟩
  exact hb'.trans ((map_sub _ p r).trans (congrArg₂ (fun a b => a - b) he ht))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
