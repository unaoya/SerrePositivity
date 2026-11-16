module

public import SerrePositivity.AlgebraicGeometry.OpenFamilyCechCoefficients

/-!
概要：元の基底からの増大を、同じタプル開と混合積の係数比較で保つ。
方針：appLE の合成則と同じ標準入射・基底の射の式を使う。
規約：元の構造層の切断と基底の Γ を保持する。
使われ方：実際の二重 Čech の増大軸。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
universe u

set_option backward.isDefEq.respectTransparency false in
/-- 同じ開の切断と大域切断の標準比較は、元の基底の射の appLE と可換。 -/
theorem openSections_appLE_top {X S : Scheme.{u}} (v : X ⟶ S) (O : X.Opens) :
    v.appLE ⊤ O (by simp) ≫ O.topIso.inv = Scheme.Γ.map (O.ι ≫ v).op := by
  have hi : O.ι.appLE O ⊤ O.ι_preimage_self.ge = O.topIso.inv := by
    simp only [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
    rfl
  rw [← hi, Scheme.Hom.appLE_comp_appLE]
  change (O.ι ≫ v).appLE ⊤ ⊤ _ = (O.ι ≫ v).appTop
  simpa only [Scheme.Hom.preimage_top] using
    (Scheme.Hom.appLE_eq_app (O.ι ≫ v) (U := ⊤))

variable {Y S : Scheme.{u}} (f : Y ⟶ S) {ι : Type} (U : ι → Y.Opens)

set_option backward.isDefEq.respectTransparency false in
/-- 元の基底からの増大は、同じ混合積の基底の Γ へ移る。 -/
theorem openFamilyCechSectionsIso_augmentation (n : SimplexCategory)
    (t : Fin (n.len + 1) → ι) :
    (WidePullback.base (fun _ : Fin (n.len + 1) ↦ f)).appLE ⊤
        (schemeCechTupleOpen f U (op n) t) (by simp) ≫
        (openFamilyCechSectionsIso f U n t).hom =
      Scheme.Γ.map (WidePullback.base (fun j ↦ (U (t j)).ι ≫ f)).op := by
  simp only [openFamilyCechSectionsIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  rw [← Category.assoc, openSections_appLE_top]
  change Scheme.Γ.map ((schemeCechTupleOpen f U (op n) t).ι ≫
      WidePullback.base (fun _ : Fin (n.len + 1) ↦ f)).op ≫
    Scheme.Γ.map (openFamilyCechIso f U n t).hom.op = _
  rw [← Scheme.Γ.map_comp, ← CategoryTheory.op_comp, ← Category.assoc,
    openFamilyCechIso_hom_fac, openFamilyCechInclusion_base]

end SerrePositivity.AlgebraicGeometry
