module

public import SerrePositivity.AlgebraicGeometry.OpenFamilyCechAugmentation
public import SerrePositivity.AlgebraicGeometry.FrobeniusDirectLimitRingIso

/-!
概要：同じタプル開と混合積の構造層の比較を、実際の Frobenius 係数へ移す。
方針：元の環同型を使い、同じ有限段の元で自然性と増大を照合する。
規約：元の appLE と全ての単体の射を保持する。
使われ方：実際の矩形タプルの二重 Čech の係数の比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
universe u
variable {Y S : Scheme.{u}} (f : Y ⟶ S) {ι : Type} (U : ι → Y.Opens)
variable (p : ℕ) (hp : p.Prime)

/-- 同じ実際の切断環の比較で、混合積の標数条件を供給する。 -/
theorem openFamilyCechMixed_primeCast (n : SimplexCategory) (t : Fin (n.len + 1) → ι)
    (hP : (p : ((Arrow.mk f).cechNerve.obj (op n)).presheaf.obj
      (op (schemeCechTupleOpen f U (op n) t))) = 0) :
    (p : Scheme.Γ.obj (op (finiteFamilyCechComponent (fun i ↦ (U i).ι ≫ f) n t))) = 0 := by
  rw [← map_natCast (openFamilyCechSectionsIso f U n t).hom.hom, hP, map_zero]

/-- 元のタプル開の係数と同じ混合積の係数の、実際の Frobenius 順極限の環同型。 -/
def openFamilyCechPerfectSectionsEquiv (n : SimplexCategory) (t : Fin (n.len + 1) → ι)
    (hP : (p : ((Arrow.mk f).cechNerve.obj (op n)).presheaf.obj
      (op (schemeCechTupleOpen f U (op n) t))) = 0) :
    FrobeniusDirectLimit (((Arrow.mk f).cechNerve.obj (op n)).presheaf.obj
        (op (schemeCechTupleOpen f U (op n) t))) p hp hP ≃+*
      FrobeniusDirectLimit (Scheme.Γ.obj
        (op (finiteFamilyCechComponent (fun i ↦ (U i).ι ≫ f) n t))) p hp
        (openFamilyCechMixed_primeCast f U p n t hP) :=
  frobeniusDirectLimitRingIso p hp hP (openFamilyCechMixed_primeCast f U p n t hP)
    (openFamilyCechSectionsIso f U n t)

/-- 同じ有限段には、元の構造層の環同型を適用する。 -/
theorem openFamilyCechPerfectSectionsEquiv_of (n : SimplexCategory)
    (t : Fin (n.len + 1) → ι)
    (hP : (p : ((Arrow.mk f).cechNerve.obj (op n)).presheaf.obj
      (op (schemeCechTupleOpen f U (op n) t))) = 0)
    (k : ℕ) (x : ((Arrow.mk f).cechNerve.obj (op n)).presheaf.obj
      (op (schemeCechTupleOpen f U (op n) t))) :
    openFamilyCechPerfectSectionsEquiv f U p hp n t hP (frobeniusDirectLimitOf _ p hp hP k x) =
      frobeniusDirectLimitOf _ p hp (openFamilyCechMixed_primeCast f U p n t hP) k
        ((openFamilyCechSectionsIso f U n t).hom.hom x) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- 元の構造層の appLE と同じ単体の射を、実際の Frobenius 比較も保つ。 -/
theorem openFamilyCechPerfectSectionsEquiv_naturality {m n : SimplexCategory} (a : m ⟶ n)
    (t : Fin (n.len + 1) → ι)
    (hM : (p : ((Arrow.mk f).cechNerve.obj (op m)).presheaf.obj
      (op (schemeCechTupleOpen f U (op m) (fun j ↦ t (a.toOrderHom j))))) = 0)
    (hN : (p : ((Arrow.mk f).cechNerve.obj (op n)).presheaf.obj
      (op (schemeCechTupleOpen f U (op n) t))) = 0)
    (z : FrobeniusDirectLimit (((Arrow.mk f).cechNerve.obj (op m)).presheaf.obj
      (op (schemeCechTupleOpen f U (op m) (fun j ↦ t (a.toOrderHom j))))) p hp hM) :
    openFamilyCechPerfectSectionsEquiv f U p hp n t hN
        (frobeniusDirectLimitMap p hp hM hN
          (((Arrow.mk f).cechNerve.map a.op).appLE
            (schemeCechTupleOpen f U (op m) (fun j ↦ t (a.toOrderHom j)))
            (schemeCechTupleOpen f U (op n) t) (schemeCechTupleOpen_map_le f U a.op t)).hom z) =
      frobeniusDirectLimitMap p hp
        (openFamilyCechMixed_primeCast f U p m (fun j ↦ t (a.toOrderHom j)) hM)
        (openFamilyCechMixed_primeCast f U p n t hN)
        (Scheme.Γ.map (finiteFamilyCechComponentMap (fun i ↦ (U i).ι ≫ f) a t).op).hom
        (openFamilyCechPerfectSectionsEquiv f U p hp m (fun j ↦ t (a.toOrderHom j)) hM z) := by
  obtain ⟨k, x, hx⟩ := DirectLimit.exists_eq_mk (frobeniusDirectSystemMap _ p hp hM) z
  change z = frobeniusDirectLimitOf _ p hp hM k x at hx
  rw [hx, frobeniusDirectLimitMap_of, openFamilyCechPerfectSectionsEquiv_of,
    openFamilyCechPerfectSectionsEquiv_of, frobeniusDirectLimitMap_of]
  apply congrArg (frobeniusDirectLimitOf _ p hp _ k)
  exact congrArg (fun g : CommRingCat.Hom _ _ ↦ g.hom x)
    (openFamilyCechSectionsIso_naturality f U a t)

set_option backward.isDefEq.respectTransparency false in
/-- 同じ基底からの増大は、実際の Frobenius 係数の比較でも保たれる。 -/
theorem openFamilyCechPerfectSectionsEquiv_augmentation
    (hS : (p : Scheme.Γ.obj (op S)) = 0) (n : SimplexCategory)
    (t : Fin (n.len + 1) → ι)
    (hN : (p : ((Arrow.mk f).cechNerve.obj (op n)).presheaf.obj
      (op (schemeCechTupleOpen f U (op n) t))) = 0)
    (z : FrobeniusDirectLimit (Scheme.Γ.obj (op S)) p hp hS) :
    openFamilyCechPerfectSectionsEquiv f U p hp n t hN
        (frobeniusDirectLimitMap p hp hS hN
          ((WidePullback.base (fun _ : Fin (n.len + 1) ↦ f)).appLE ⊤
            (schemeCechTupleOpen f U (op n) t) (by simp)).hom z) =
      frobeniusDirectLimitMap p hp hS (openFamilyCechMixed_primeCast f U p n t hN)
        (Scheme.Γ.map (WidePullback.base (fun j ↦ (U (t j)).ι ≫ f)).op).hom z := by
  obtain ⟨k, x, hx⟩ := DirectLimit.exists_eq_mk (frobeniusDirectSystemMap _ p hp hS) z
  change z = frobeniusDirectLimitOf _ p hp hS k x at hx
  rw [hx, frobeniusDirectLimitMap_of, openFamilyCechPerfectSectionsEquiv_of,
    frobeniusDirectLimitMap_of]
  apply congrArg (frobeniusDirectLimitOf _ p hp _ k)
  exact congrArg (fun g : CommRingCat.Hom _ _ ↦ g.hom x)
    (openFamilyCechSectionsIso_augmentation f U n t)

end SerrePositivity.AlgebraicGeometry
