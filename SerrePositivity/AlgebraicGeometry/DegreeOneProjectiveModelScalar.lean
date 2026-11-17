module

public import SerrePositivity.AlgebraicGeometry.DegreeOneProjectiveModel
public import SerrePositivity.AlgebraicGeometry.SchemeBlowupAway

/-!
概要：実際の射影表示の同型で、スカラー・閉中心・中心外の条件を保つ。
方針：同じ over の等式と Γ–Spec の自然性、Cartesian square の同型移送を使う。
規約：閉中心の空間と商の構造射を固定する。
使われ方：F8 の入力を実際のブローアップの入力から供給する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {R : Type u} [CommRing R] {Y : Scheme.{u}}
variable {f : Y ⟶ Spec (CommRingCat.of R)} (m : DegreeOneProjectiveModel f)

set_option backward.isDefEq.respectTransparency false in
/-- 表示の同型は元の構造射の大域スカラーを保つ。 -/
theorem DegreeOneProjectiveModel.scalarHom :
    schemeScalarHom Y f = m.iso.hom.appTop.hom.comp
      (projectiveScalarToGlobalSections m.grade) := by
  have h := schemeScalarHom_naturality (Proj m.grade) m.iso.hom
    (projectiveCechStructureMap m.grade) f (RingHom.id R)
    (by simpa using m.over)
  change (schemeScalarHom Y f).comp (RingHom.id R) =
    m.iso.hom.appTop.hom.comp
      (schemeScalarHom (Proj m.grade)
        (schemeScalarMorphism (Proj m.grade) (projectiveScalarToGlobalSections m.grade))) at h
  rw [schemeScalarHom_scalarMorphism] at h
  simpa using h

/-- 表示の同型で右上だけを動かした、同じ閉中心の Cartesian square。 -/
theorem DegreeOneProjectiveModel.cartesian {S : Type u} [CommRing S]
    {X : Scheme.{u}} (g : X ⟶ Y) (iX : X ⟶ Spec (CommRingCat.of S))
    (q : R →+* S) (H : IsPullback g iX f (Spec.map (CommRingCat.ofHom q))) :
    IsPullback (g ≫ m.iso.hom) iX (projectiveCechStructureMap m.grade)
      (Spec.map (CommRingCat.ofHom q)) := by
  apply H.of_iso (Iso.refl X) m.iso (Iso.refl _) (Iso.refl _)
  · simp
  · simp
  · simpa using m.over.symm
  · simp

/-- 元の構造射の全射性は、同じ表示の Proj の構造射にも成り立つ。 -/
theorem DegreeOneProjectiveModel.structure_surjective [Surjective f] :
    Surjective (projectiveCechStructureMap m.grade) := by
  have : Surjective (m.iso.hom ≫ projectiveCechStructureMap m.grade) := by
    rw [m.over]
    infer_instance
  exact Surjective.of_comp m.iso.hom (projectiveCechStructureMap m.grade)

set_option backward.isDefEq.respectTransparency false in
/-- 元の構造射の開集合上の同型性は、同じ表示の Proj の構造射に移る。 -/
theorem DegreeOneProjectiveModel.restrict_isIso (W : (Spec (CommRingCat.of R)).Opens)
    [IsIso (f ∣_ W)] : IsIso (projectiveCechStructureMap m.grade ∣_ W) := by
  have : IsIso (f ∣_ (Iso.refl (Spec (CommRingCat.of R))).inv ⁻¹ᵁ W) := by
    change IsIso (f ∣_ (𝟙 (Spec (CommRingCat.of R))) ⁻¹ᵁ W)
    rw [Scheme.Hom.id_preimage]
    infer_instance
  apply isIso_restrict_of_iso_comparison (projectiveCechStructureMap m.grade) f
    m.iso (Iso.refl _) (by simpa using m.over) W

end SerrePositivity.AlgebraicGeometry
