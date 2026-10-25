module

public import SerrePositivity.InfinityCategories.Core.LimitDiagramIso
public import SerrePositivity.InfinityCategories.Core.EquivalenceAllLimits

/-!
概要：図式の関手同型に沿って、指定関手も保存する極限全錐を輸送する。
方針：可逆円柱全体へ元の錐を延長し、像でも始点制限の同値から極限性を反映する。
規約：錐とその像を同時に輸送し、関手一般の保存性は仮定しない。
使われ方：filtered 補完の全錐を元の Ind 図式へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 図式の関手同型は、同じ指定関手に保存される極限全錐の存在を保つ。 -/
lemma exists_limitCone_of_functorIso_with_image {K X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (F : X ⟶ Y) {p q : K ⟶ X}
    (e : FunctorIso p q) (c : JoinCone p) (hc : IsLimitCone c)
    (hF : IsLimitCone (mapJoinCone F c)) :
    ∃ d : JoinCone q, IsLimitCone d ∧ IsLimitCone (mapJoinCone F d) := by
  obtain ⟨H, h0, h1⟩ := exists_equivalenceCylinder_extension_of_functorIso e
  let f0 := equivalenceCylinderEndpoint K false
  let f1 := equivalenceCylinderEndpoint K true
  have hf0 := isPrecompositionEquivalence_equivalenceCylinderEndpoint K false
  have hf1 := isPrecompositionEquivalence_equivalenceCylinderEndpoint K true
  have h0' : f0 ≫ H = p := h0
  have h1' : f1 ≫ H = q := h1
  let c0 : JoinCone (f0 ≫ H) := ⟨c.val, c.property.trans h0'.symm⟩
  have hc0 : IsLimitCone c0 :=
    (isLimitCone_iff_of_diagram_eq (d := c) h0' rfl).mpr hc
  have : TrivialKanFibration (sliceOverRestrict H f0) :=
    sliceOverRestrict_trivialKanFibration_of_precompositionEquivalence H f0 hf0
  obtain ⟨a, ha, har, _⟩ := exists_limitCone_extension_of_trivialRestriction H f0 c0 hc0
  have him : IsLimitCone (mapJoinCone F a) := by
    have : TrivialKanFibration (sliceOverRestrict (H ≫ F) f0) :=
      sliceOverRestrict_trivialKanFibration_of_precompositionEquivalence (H ≫ F) f0 hf0
    apply ((qCatEquivalenceOfTrivialKanFibration
      (sliceOverRestrict (H ≫ F) f0)).isTerminalVertex_iff (mapJoinCone F a)).mpr
    change IsLimitCone (restrictJoinCone (mapJoinCone F a) f0)
    have hv : (restrictJoinCone (mapJoinCone F a) f0).val =
        (mapJoinCone F c).val := by
      change (joinMap (𝟙 _) f0 ≫ a.val) ≫ F = c.val ≫ F
      exact congrArg (fun z ↦ z ≫ F) (congrArg Subtype.val har)
    have hd := (restrictJoinCone (mapJoinCone F a) f0).property.symm.trans
      ((congrArg (fun z ↦ joinInr _ _ ≫ z) hv).trans (mapJoinCone F c).property)
    exact (isLimitCone_iff_of_diagram_eq (d := mapJoinCone F c) hd hv).mpr hF
  have : TrivialKanFibration (sliceOverRestrict H f1) :=
    sliceOverRestrict_trivialKanFibration_of_precompositionEquivalence H f1 hf1
  let b := restrictJoinCone a f1
  have hb : IsLimitCone b :=
    ((qCatEquivalenceOfTrivialKanFibration (sliceOverRestrict H f1)).isTerminalVertex_iff a).mp ha
  let d : JoinCone q := ⟨b.val, b.property.trans h1'⟩
  have hd : IsLimitCone d :=
    (isLimitCone_iff_of_diagram_eq (d := b) h1'.symm rfl).mpr hb
  refine ⟨d, hd, ?_⟩
  have : TrivialKanFibration (sliceOverRestrict (H ≫ F) f1) :=
    sliceOverRestrict_trivialKanFibration_of_precompositionEquivalence (H ≫ F) f1 hf1
  have hbi := ((qCatEquivalenceOfTrivialKanFibration
    (sliceOverRestrict (H ≫ F) f1)).isTerminalVertex_iff (mapJoinCone F a)).mp him
  apply (isLimitCone_iff_of_diagram_eq
    (d := restrictJoinCone (mapJoinCone F a) f1) ?_ ?_).mpr hbi
  · exact (congrArg (fun z ↦ z ≫ F) h1').symm.trans (Category.assoc _ _ _)
  · rfl

end SerrePositivity.InfinityCategories
