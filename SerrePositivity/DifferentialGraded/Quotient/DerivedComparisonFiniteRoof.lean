module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonUnitCone
public import SerrePositivity.DifferentialGraded.Verdier.Tria

/-! # 比較 cone の有限因子分解性から Verdier 分母を作る

有限 cell の始域から局所化対象への射を、有限 cell の分母を使って持ち上げる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma derivedFiniteCell_subset_univ (S : Set D) :
    derivedFiniteCellOver A D S ≤ derivedFiniteCellOver A D Set.univ :=
  (derivedFiniteCellOver_le_iff_generators A D
    (derivedFiniteCellOver A D Set.univ) S).2 (fun x _ =>
      (moduleFiniteCellOver A D Set.univ).prop_map_obj (moduleToDerived A D)
        (moduleFiniteCell_representable A D x))

/-- 指定有限 cell を経由する射は、その cone も指定有限 cell である分母で消せる。 -/
lemma finiteCellFactor_exists_denominator (S : Set D)
    {X Y : DerivedModuleCategory A D} (hX : derivedFiniteCellOver A D Set.univ X)
    (f : X ⟶ Y) (hf : ModuleFiniteCellFactor A D S f) :
    ∃ (E : DerivedModuleCategory A D), derivedFiniteCellOver A D Set.univ E ∧
      ∃ s : E ⟶ X, (derivedFiniteCellOver A D S).trW s ∧ s ≫ f = 0 := by
  obtain ⟨P, hP, a, b, hab⟩ := hf
  obtain ⟨E, s, δ, hT⟩ := distinguished_cocone_triangle₁ a
  have hE := (derivedFiniteCellOver A D Set.univ).ext_of_isTriangulatedClosed₁
    _ hT hX (derivedFiniteCell_subset_univ A D S P hP)
  refine ⟨E, hE, s, ObjectProperty.trW.mk _ hT hP, ?_⟩
  have hs0 : s ≫ a = 0 := comp_distTriang_mor_zero₁₂ _ hT
  rw [← hab, ← Category.assoc, hs0, zero_comp]

/-- cone が有限因子分解性を持つ比較三角形に対する、有限 cell 始域の射の roof 表示。 -/
lemma finiteCellRoof_of_cone_factorTarget (S : Set D)
    (T : Triangle (DerivedModuleCategory A D))
    (hT : T ∈ distTriang (DerivedModuleCategory A D))
    (hC : moduleFiniteCellFactorTarget A D S T.obj₃)
    {X : DerivedModuleCategory A D} (hX : derivedFiniteCellOver A D Set.univ X)
    (f : X ⟶ T.obj₂) :
    ∃ (E : DerivedModuleCategory A D), derivedFiniteCellOver A D Set.univ E ∧
      ∃ (s : E ⟶ X) (g : E ⟶ T.obj₁),
        (derivedFiniteCellOver A D S).trW s ∧ g ≫ T.mor₁ = s ≫ f := by
  have hc : moduleCompact A D X := modulePerfectOver_compact A D
    ((derivedFiniteCellOver A D Set.univ).le_retractClosure X hX)
  obtain ⟨E, hE, s, hs, hz⟩ := finiteCellFactor_exists_denominator A D S hX
    (f ≫ T.mor₂) (hC X hc (f ≫ T.mor₂))
  obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₂ T hT (s ≫ f)
    (by rw [Category.assoc]; exact hz)
  exact ⟨E, hE, s, g, hs, hg.symm⟩

/-- 比較後に零になる射は、比較 cone の逆 shift を経由して有限 cell に因子分解する。 -/
lemma finiteCellFactor_of_comparison_zero (S : Set D)
    (T : Triangle (DerivedModuleCategory A D))
    (hT : T ∈ distTriang (DerivedModuleCategory A D))
    (hC : moduleFiniteCellFactorTarget A D S T.obj₃)
    {X : DerivedModuleCategory A D} (hX : moduleCompact A D X)
    (f : X ⟶ T.obj₁) (hf : f ≫ T.mor₁ = 0) :
    ModuleFiniteCellFactor A D S f := by
  obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₂ T.invRotate
    (inv_rot_of_distTriang _ hT) f hf
  rw [hg]
  exact (moduleFiniteCellFactorTarget_shift A D hC (-1) X hX g).postcompose A D _

/-- 比較後に零になる射は、指定有限 cell の cone を持つ分母で既に零になる。 -/
lemma comparison_zero_exists_finiteCell_denominator (S : Set D)
    (T : Triangle (DerivedModuleCategory A D))
    (hT : T ∈ distTriang (DerivedModuleCategory A D))
    (hC : moduleFiniteCellFactorTarget A D S T.obj₃)
    {X : DerivedModuleCategory A D} (hX : derivedFiniteCellOver A D Set.univ X)
    (f : X ⟶ T.obj₁) (hf : f ≫ T.mor₁ = 0) :
    ∃ (E : DerivedModuleCategory A D), derivedFiniteCellOver A D Set.univ E ∧
      ∃ s : E ⟶ X, (derivedFiniteCellOver A D S).trW s ∧ s ≫ f = 0 :=
  finiteCellFactor_exists_denominator A D S hX f
    (finiteCellFactor_of_comparison_zero A D S T hT hC
      (modulePerfectOver_compact A D
        ((derivedFiniteCellOver A D Set.univ).le_retractClosure X hX)) f hf)

/-- 商の制限代表加群への任意の有限 cell 始域の射は、Verdier 分母の後で持ち上がる。 -/
lemma quotientRepresentable_exists_finiteCellRoof (S : Set D)
    (h : localKFlat A D S) (z : D)
    {X : DerivedModuleCategory A D} (hX : derivedFiniteCellOver A D Set.univ X)
    (f : X ⟶ (moduleToDerived A D).obj
      (ForgetEnrichment.of (Complex A) (quotientRepresentableRestriction A D S z))) :
    ∃ (E : DerivedModuleCategory A D), derivedFiniteCellOver A D Set.univ E ∧
      ∃ (s : E ⟶ X)
        (g : E ⟶ (moduleToDerived A D).obj
          (ForgetEnrichment.of (Complex A) (representable A z))),
        (derivedFiniteCellOver A D S).trW s ∧
        g ≫ (moduleToDerived A D).map
          (representableRestrictionMap A D (QuotientObject D S) (inclusion A D S) z) = s ≫ f :=
  finiteCellRoof_of_cone_factorTarget A D S _
    (moduleDerivedConeTriangle_distinguished A D
      (representableRestrictionMap A D (QuotientObject D S) (inclusion A D S) z))
    (quotientRepresentableComparisonCone_finiteCellFactorTarget A D S h z) hX f

/-- 同じ roof を、U17a の tria(D) とその指定 Verdier 分母の中で表す。 -/
lemma quotientRepresentable_exists_triaRoof (S : Set D)
    (h : localKFlat A D S) (z : D) (X : TriaCategory A D)
    (f : (triaInclusion A D).obj X ⟶ (moduleToDerived A D).obj
      (ForgetEnrichment.of (Complex A) (quotientRepresentableRestriction A D S z))) :
    ∃ (E : TriaCategory A D) (s : E ⟶ X) (g : E ⟶ triaRepresentable A D z),
      (triaImage A D S).trW s ∧
        (triaInclusion A D).map g ≫ (moduleToDerived A D).map
          (representableRestrictionMap A D (QuotientObject D S) (inclusion A D S) z) =
            (triaInclusion A D).map s ≫ f := by
  obtain ⟨E, hE, s, g, hs, hg⟩ :=
    quotientRepresentable_exists_finiteCellRoof A D S h z X.property f
  let E' : TriaCategory A D := ⟨E, hE⟩
  let s' : E' ⟶ X := ObjectProperty.homMk s
  let g' : E' ⟶ triaRepresentable A D z := ObjectProperty.homMk g
  refine ⟨E', s', g', ?_, hg⟩
  exact ((derivedFiniteCellOver A D S).inverseImage_trW_iff (triaInclusion A D) s').2 hs

/-- U17a の局所化で、代表加群比較の核に入る射は零になる。 -/
lemma triaQuotient_map_eq_zero_of_representableComparison (S : Set D)
    (h : localKFlat A D S) (z : D) (X : TriaCategory A D)
    (f : X ⟶ triaRepresentable A D z)
    (hf : (triaInclusion A D).map f ≫ (moduleToDerived A D).map
      (representableRestrictionMap A D (QuotientObject D S) (inclusion A D S) z) = 0) :
    (triaQuotient A D S).map f = 0 := by
  obtain ⟨E, hE, s, hs, hz⟩ := comparison_zero_exists_finiteCell_denominator A D S
    (moduleDerivedConeTriangle A D
      (representableRestrictionMap A D (QuotientObject D S) (inclusion A D S) z))
    (moduleDerivedConeTriangle_distinguished A D
      (representableRestrictionMap A D (QuotientObject D S) (inclusion A D S) z))
    (quotientRepresentableComparisonCone_finiteCellFactorTarget A D S h z)
    X.property ((triaInclusion A D).map f) hf
  let E' : TriaCategory A D := ⟨E, hE⟩
  let s' : E' ⟶ X := ObjectProperty.homMk s
  have hs' : (triaImage A D S).trW s' :=
    ((derivedFiniteCellOver A D S).inverseImage_trW_iff (triaInclusion A D) s').2 hs
  have hz' : s' ≫ f = 0 := by
    apply (triaInclusion A D).map_injective
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_zero]
    change s ≫ (triaInclusion A D).map f = 0
    exact hz
  have : IsIso ((triaQuotient A D S).map s') :=
    Localization.inverts (triaQuotient A D S) (triaImage A D S).trW s' hs'
  apply (cancel_epi ((triaQuotient A D S).map s')).1
  rw [← CategoryTheory.Functor.map_comp, hz', CategoryTheory.Functor.map_zero,
    Limits.comp_zero]

end SerrePositivity.DifferentialGraded.DGQuotient
