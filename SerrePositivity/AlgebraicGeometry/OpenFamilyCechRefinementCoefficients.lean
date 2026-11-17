module

public import SerrePositivity.AlgebraicGeometry.OpenFamilyCechRefinement
public import SerrePositivity.AlgebraicGeometry.OpenFamilyCechCoefficients

/-!
概要：同じ開の細分を、元の構造層と混合積の切断の標準比較で保つ。
方針：開の包含への resLE の切断の公式と、同じ幾何的標準比較を使う。
規約：元の制限写像と添字の写像を保持する。
使われ方：矩形の縦方向の係数移送の自然性。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
universe u

set_option backward.isDefEq.respectTransparency false in
/-- 同じ開の包含の Γ は、元の前層の制限と標準的に一致する。 -/
theorem openSections_homOfLE {X : Scheme.{u}} {M N : X.Opens} (e : N ≤ M) :
    M.topIso.hom ≫ X.presheaf.map (homOfLE e).op ≫ N.topIso.inv =
      Scheme.Γ.map (X.homOfLE e).op := by
  have h := Scheme.Hom.resLE_app_top (𝟙 X) e
  rw [Scheme.Hom.resLE_id] at h
  simp only [Scheme.Hom.appLE, Scheme.Hom.id_app, Category.id_comp] at h
  exact h.symm

variable {Y S : Scheme.{u}} (f : Y ⟶ S) {ι κ : Type}
variable (U : ι → Y.Opens) (V : κ → Y.Opens) (ρ : κ → ι) (hV : ∀ j, V j ≤ U (ρ j))

set_option backward.isDefEq.respectTransparency false in
/-- 同じタプル開の切断と混合積の比較は、元の開の細分の制限に自然。 -/
theorem openFamilyCechSectionsIso_refinement (n : SimplexCategory) (t : Fin (n.len + 1) → κ) :
    ((Arrow.mk f).cechNerve.obj (op n)).presheaf.map
        (homOfLE (openFamilyCechRefinementOpen_le f U V ρ hV n t)).op ≫
        (openFamilyCechSectionsIso f V n t).hom =
      (openFamilyCechSectionsIso f U n (fun j ↦ ρ (t j))).hom ≫
        Scheme.Γ.map (openFamilyCechRefinementMap f U V ρ hV n t).op := by
  let M := schemeCechTupleOpen f U (op n) (fun j ↦ ρ (t j))
  let N := schemeCechTupleOpen f V (op n) t
  let e := openFamilyCechRefinementOpen_le f U V ρ hV n t
  have ht : M.topIso.hom ≫
      ((Arrow.mk f).cechNerve.obj (op n)).presheaf.map (homOfLE e).op ≫ N.topIso.inv =
      Scheme.Γ.map (((Arrow.mk f).cechNerve.obj (op n)).homOfLE e).op :=
    openSections_homOfLE e
  have hg := congrArg (fun g ↦ Scheme.Γ.map g.op)
    (openFamilyCechRefinementMap_iso f U V ρ hV n t)
  simp only [CategoryTheory.op_comp, CategoryTheory.Functor.map_comp] at hg
  simp only [openFamilyCechSectionsIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  change ((Arrow.mk f).cechNerve.obj (op n)).presheaf.map (homOfLE e).op ≫
      (N.topIso.inv ≫ Scheme.Γ.map (openFamilyCechIso f V n t).hom.op) =
    (M.topIso.inv ≫ Scheme.Γ.map (openFamilyCechIso f U n (fun j ↦ ρ (t j))).hom.op) ≫ _
  calc
    _ = M.topIso.inv ≫ (M.topIso.hom ≫
        ((Arrow.mk f).cechNerve.obj (op n)).presheaf.map (homOfLE e).op ≫ N.topIso.inv) ≫
        Scheme.Γ.map (openFamilyCechIso f V n t).hom.op := by
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
    _ = M.topIso.inv ≫
        Scheme.Γ.map (((Arrow.mk f).cechNerve.obj (op n)).homOfLE e).op ≫
        Scheme.Γ.map (openFamilyCechIso f V n t).hom.op := by rw [ht]
    _ = _ := by rw [Category.assoc, ← hg, ← Category.assoc]

end SerrePositivity.AlgebraicGeometry
