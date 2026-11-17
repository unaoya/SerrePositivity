module

public import SerrePositivity.AlgebraicGeometry.OpenFamilyCechComparison

/-!
概要：元のタプル開の構造層の切断を、同じ混合積の Γ と比較する。
方針：開の標準同型と Opens.topIso を合成し、resLE の切断の公式を使う。
規約：元の構造層の appLE と全ての単体の射を保持する。
使われ方：同じ矩形タプルの実際の係数図式の比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
universe u
variable {Y S : Scheme.{u}} (f : Y ⟶ S) {ι : Type} (U : ι → Y.Opens)

set_option backward.isDefEq.respectTransparency false in
/-- 同じ制限の写像は、元の nerve の resLE そのもの。 -/
theorem openFamilyCechOpenMap_eq_resLE {m n : SimplexCategory} (a : m ⟶ n)
    (t : Fin (n.len + 1) → ι) :
    openFamilyCechOpenMap f U a t = ((Arrow.mk f).cechNerve.map a.op).resLE
      (schemeCechTupleOpen f U (op m) (fun j ↦ t (a.toOrderHom j)))
      (schemeCechTupleOpen f U (op n) t) (schemeCechTupleOpen_map_le f U a.op t) := by
  apply (cancel_mono
    (schemeCechTupleOpen f U (op m) (fun j ↦ t (a.toOrderHom j))).ι).mp
  rw [openFamilyCechOpenMap_fac, Scheme.Hom.resLE_comp_ι]

/-- 元のタプル開の実際の切断環と、同じ混合積の切断環の標準同型。 -/
def openFamilyCechSectionsIso (n : SimplexCategory) (t : Fin (n.len + 1) → ι) :
    ((Arrow.mk f).cechNerve.obj (op n)).presheaf.obj (op (schemeCechTupleOpen f U (op n) t)) ≅
      Scheme.Γ.obj (op (finiteFamilyCechComponent (fun i ↦ (U i).ι ≫ f) n t)) :=
  (schemeCechTupleOpen f U (op n) t).topIso.symm ≪≫
    Scheme.Γ.mapIso (openFamilyCechIso f U n t).op

set_option backward.isDefEq.respectTransparency false in
/-- 同じ係数の標準比較は、元の構造層の appLE と全ての単体の射に自然。 -/
theorem openFamilyCechSectionsIso_naturality {m n : SimplexCategory} (a : m ⟶ n)
    (t : Fin (n.len + 1) → ι) :
    ((Arrow.mk f).cechNerve.map a.op).appLE
        (schemeCechTupleOpen f U (op m) (fun j ↦ t (a.toOrderHom j)))
        (schemeCechTupleOpen f U (op n) t) (schemeCechTupleOpen_map_le f U a.op t) ≫
        (openFamilyCechSectionsIso f U n t).hom =
      (openFamilyCechSectionsIso f U m (fun j ↦ t (a.toOrderHom j))).hom ≫
        Scheme.Γ.map (finiteFamilyCechComponentMap (fun i ↦ (U i).ι ≫ f) a t).op := by
  let M := schemeCechTupleOpen f U (op m) (fun j ↦ t (a.toOrderHom j))
  let N := schemeCechTupleOpen f U (op n) t
  let v := (Arrow.mk f).cechNerve.map a.op
  let e := schemeCechTupleOpen_map_le f U a.op t
  have ht : M.topIso.hom ≫ v.appLE M N e ≫ N.topIso.inv =
      Scheme.Γ.map (openFamilyCechOpenMap f U a t).op := by
    rw [openFamilyCechOpenMap_eq_resLE]
    exact (Scheme.Hom.resLE_app_top v e).symm
  have hg := congrArg (fun g ↦ Scheme.Γ.map g.op) (openFamilyCechIso_naturality f U a t)
  simp only [CategoryTheory.op_comp, CategoryTheory.Functor.map_comp] at hg
  simp only [openFamilyCechSectionsIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  change v.appLE M N e ≫ (N.topIso.inv ≫ Scheme.Γ.map (openFamilyCechIso f U n t).hom.op) =
    (M.topIso.inv ≫ Scheme.Γ.map
      (openFamilyCechIso f U m (fun j ↦ t (a.toOrderHom j))).hom.op) ≫ _
  calc
    _ = M.topIso.inv ≫ (M.topIso.hom ≫ v.appLE M N e ≫ N.topIso.inv) ≫
        Scheme.Γ.map (openFamilyCechIso f U n t).hom.op := by
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
    _ = M.topIso.inv ≫ Scheme.Γ.map (openFamilyCechOpenMap f U a t).op ≫
        Scheme.Γ.map (openFamilyCechIso f U n t).hom.op := by rw [ht]
    _ = _ := by rw [Category.assoc, ← hg, ← Category.assoc]

end SerrePositivity.AlgebraicGeometry
