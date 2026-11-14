module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.DGNativeDerivedDenominators
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGClosedVerdierDenominators

/-! # 全整数シフトでの商比較の分数表示

概要：シフトされた商の制限代表への導来射を、元の実分母と閉加群分子で表示する。
方針：シフトされた比較三角形の有限 cell roof と、代表加群の射影性を使う。
規約：分母は元の dg 対象からの実辺。使われ方：高次 Hom の障害と充填候補の回収。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded DGQuotient Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]

/-- 任意次数の商代表への射は、元の実分母とシフトされた閉加群分子で表示できる。 -/
theorem dgQuotientShifted_exists_closedRoof (P : Set D) (hP : localKFlat A D P)
    (x y : D) (n : ℤ)
    (f : (moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A x)) ⟶
      ((moduleToDerived A D).obj (ForgetEnrichment.of (Complex A)
        (quotientRepresentableRestriction A D P y)))⟦n⟧) :
    ∃ (q : D) (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) x)
      (g : ForgetEnrichment.of (Complex A) (representable A q) ⟶
        (ForgetEnrichment.of (Complex A) (representable A y) : ModuleCategory A D)⟦n⟧),
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P ∧
        (moduleToDerived A D).map g ≫ ((moduleToDerived A D).commShiftIso n).hom.app
          (ForgetEnrichment.of (Complex A) (representable A y)) ≫
            ((moduleToDerived A D).map (representableRestrictionMap A D
              (QuotientObject D P) (inclusion A D P) y))⟦n⟧' =
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableDerivedMap A D s ≫ f := by
  let L := moduleToDerived A D
  let T := moduleDerivedConeTriangle A D
    (representableRestrictionMap A D (QuotientObject D P) (inclusion A D P) y)
  have hT := moduleDerivedConeTriangle_distinguished A D
    (representableRestrictionMap A D (QuotientObject D P) (inclusion A D P) y)
  have hx := (moduleFiniteCellOver A D Set.univ).prop_map_obj L
    (moduleFiniteCell_representable A D x)
  obtain ⟨E, hE, s, g, hs, hg⟩ := finiteCellRoof_of_cone_factorTarget A D P
    (T⟦n⟧) (Triangle.shift_distinguished T hT n)
    (moduleFiniteCellFactorTarget_shift A D
      (quotientRepresentableComparisonCone_finiteCellFactorTarget A D P hP y) n) hx f
  obtain ⟨q, i, t, ht, htw⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgDerivedDenominator_exists_closed A D P x hE s hs
  let g' := n.negOnePow • g
  have hg' : g' ≫ (L.map (representableRestrictionMap A D
      (QuotientObject D P) (inclusion A D P) y))⟦n⟧' = s ≫ f := by
    exact (Linear.units_smul_comp _ _ _).trans
      ((Linear.comp_units_smul _ _ _).symm.trans hg)
  obtain ⟨a, ha⟩ := moduleProjectiveToDerived_map_surjective A D
    (representable_homotopicallyProjective A D q)
    (i.hom ≫ g' ≫ (L.commShiftIso n).inv.app
      (ForgetEnrichment.of (Complex A) (representable A y)))
  refine ⟨q, t, a, (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge_mem_iff_derived_trW A D P t).mpr htw, ?_⟩
  rw [ha, Category.assoc, Category.assoc, Iso.inv_hom_id_app_assoc, hg', ht, Category.assoc]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
