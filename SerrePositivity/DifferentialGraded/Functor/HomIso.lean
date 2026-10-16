module
public import SerrePositivity.DifferentialGraded.Functor.Basic

/-! # 全Homの同型から閉零圏・H⁰の完全忠実性へ

全Hom写像がchain isoであるdg関手について、逆chain mapで境界を反映する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.DGFunctor
open CategoryTheory MonoidalCategory HomologicalComplex
variable {A : Type u} [CommRing A] {D : Type v} {E : Type w}
  [DGCategory A D] [DGCategory A E] (F : DGFunctor A D E)
  (hF : ∀ x y, IsIso (F.map x y))

include hF

/-- 全Hom写像が同型なら閉零関手は充満。 -/
lemma onClosed_full_of_homIso : F.onClosed.Full where
  map_surjective {x y} f := by
    let := hF x y
    let f' : 𝟙_ (Complex A) ⟶ homObject A E (F.obj x) (F.obj y) :=
      ForgetEnrichment.homTo (Complex A) f
    change ∃ g : 𝟙_ (Complex A) ⟶ homObject A D x y, g ≫ F.map x y = f'
    refine ⟨f' ≫ inv (F.map x y), ?_⟩
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/-- 全Hom写像が同型なら閉零関手は忠実。 -/
lemma onClosed_faithful_of_homIso : F.onClosed.Faithful where
  map_injective {x y} f g h := by
    let := hF x y
    exact (cancel_mono (F.map x y)).mp h

/-- Homの逆chain mapにより、dg関手は境界関係を反映する。 -/
lemma boundary_iff_of_homIso {x y : ClosedCategory A D} (f g : x ⟶ y) :
    boundaryRelation A E (F.onClosed.map f) (F.onClosed.map g) ↔
      boundaryRelation A D f g := by
  constructor
  · rintro ⟨h⟩
    let := hF x y
    have h' : Homotopy
        ((ForgetEnrichment.homTo (Complex A) f ≫ F.map x y) ≫ inv (F.map x y))
        ((ForgetEnrichment.homTo (Complex A) g ≫ F.map x y) ≫ inv (F.map x y)) :=
      h.compRight (inv (F.map x y))
    change Nonempty (Homotopy (ForgetEnrichment.homTo (Complex A) f)
      (ForgetEnrichment.homTo (Complex A) g))
    simpa only [Category.assoc, IsIso.hom_inv_id, Category.comp_id] using Nonempty.intro h'
  · exact F.preserves_boundary f g

/-- 全Homが同型ならH⁰関手は充満。 -/
lemma onHomotopy_full_of_homIso : F.onHomotopy.Full where
  map_surjective {x y} f := by
    let := F.onClosed_full_of_homIso hF
    obtain ⟨x⟩ := x
    obtain ⟨y⟩ := y
    obtain ⟨f, rfl⟩ := (toHomotopy A E).map_surjective f
    obtain ⟨g, rfl⟩ := F.onClosed.map_surjective f
    exact ⟨(toHomotopy A D).map g, rfl⟩

/-- 全Homが同型ならH⁰関手は忠実。 -/
lemma onHomotopy_faithful_of_homIso : F.onHomotopy.Faithful where
  map_injective {x y} f g h := by
    obtain ⟨f, rfl⟩ := (toHomotopy A D).map_surjective f
    obtain ⟨g, rfl⟩ := (toHomotopy A D).map_surjective g
    exact (toHomotopy_map_eq_iff A D f g).mpr
      ((F.boundary_iff_of_homIso hF f g).mp ((toHomotopy_map_eq_iff A E _ _).mp h))

end SerrePositivity.DifferentialGraded.DGFunctor
