module
public import SerrePositivity.DifferentialGraded.Perfect.Generators

/-! # compact対象からのHomによる主導来圏の同型判定 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma compactHom_shift_postcompose_injective {X Y : DerivedModuleCategory A D} (f : X ⟶ Y)
    (hInj : ∀ P : DerivedModuleCategory A D, moduleCompact A D P →
      Function.Injective (fun a : P ⟶ X => a ≫ f))
    (P : DerivedModuleCategory A D) (hP : moduleCompact A D P) :
    Function.Injective (fun a : P ⟶ X⟦(1 : ℤ)⟧ => a ≫ f⟦(1 : ℤ)⟧') := by
  let adj := (shiftEquiv' (DerivedModuleCategory A D) (-1) 1 (neg_add_cancel (1 : ℤ))).toAdjunction
  intro a b hab
  apply (adj.homEquiv P X).symm.injective
  apply hInj (P⟦(-1 : ℤ)⟧) (moduleCompact_shift A D hP (-1))
  change (adj.homEquiv P X).symm a ≫ f = (adj.homEquiv P X).symm b ≫ f
  rw [← adj.homEquiv_naturality_right_symm, ← adj.homEquiv_naturality_right_symm]
  exact congrArg ((adj.homEquiv P Y).symm) hab

/-- 既存の代表加群shiftによる零性検出を用いる。compact⇒Perfは仮定しない。 -/
lemma moduleDerived_isIso_of_compact_hom_bijective {X Y : DerivedModuleCategory A D}
    (f : X ⟶ Y)
    (hBij : ∀ P : DerivedModuleCategory A D, moduleCompact A D P →
      Function.Bijective (fun a : P ⟶ X => a ≫ f)) : IsIso f := by
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle f
  let T := Triangle.mk f g h
  have hz : IsZero Z := by
    apply (moduleCompactGenerators_detect_zero A D Z).2
    intro p
    let P := moduleCompactGenerators A D p
    have hP : moduleCompact A D P := moduleCompactGenerators_compact A D p
    have ha (a : P ⟶ Z) : a = 0 := by
      have hw : a ≫ h = 0 := by
        apply compactHom_shift_postcompose_injective A D f
          (fun Q hQ => (hBij Q hQ).1) P hP
        change (a ≫ h) ≫ f⟦(1 : ℤ)⟧' = 0 ≫ f⟦(1 : ℤ)⟧'
        have ht := comp_distTriang_mor_zero₃₁ T hT
        change h ≫ f⟦(1 : ℤ)⟧' = 0 at ht
        rw [zero_comp, Category.assoc, ht, comp_zero]
      obtain ⟨b, hb⟩ := T.coyoneda_exact₃ hT a hw
      obtain ⟨c, hc⟩ := (hBij P hP).2 b
      change c ≫ f = b at hc
      have hfg := comp_distTriang_mor_zero₁₂ T hT
      change f ≫ g = 0 at hfg
      rw [hb, ← hc, Category.assoc]
      change c ≫ f ≫ g = 0
      rw [hfg, comp_zero]
    exact ⟨fun a b => (ha a).trans (ha b).symm⟩
  exact (T.isZero₃_iff_isIso₁ hT).1 hz

end SerrePositivity.DifferentialGraded
