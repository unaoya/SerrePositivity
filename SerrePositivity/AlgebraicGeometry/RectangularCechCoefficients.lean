module

public import SerrePositivity.AlgebraicGeometry.RectangularCechTupleIntersection
public import SerrePositivity.AlgebraicGeometry.OpenFamilyCechAugmentation

/-!
概要：元の full Čech の交叉上の切断環を、同じ矩形の混合積の Γ へ移す。
方針：元の開の等号と同じタプル開の標準比較を合成する。
規約：元の有限像の交叉と基底からの appLE を保持する。
使われ方：実際の二重 Čech の行の係数比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
universe u
variable {Y S : Scheme.{u}} (f : Y ⟶ S) {ι : Type} [DecidableEq ι] (U : ι → Y.Opens)

/-- 元の full Čech の実際の交叉と、同じ矩形の混合積の切断環の標準同型。 -/
def rectangularCechSectionsIso (n : SimplexCategory) (k : ℕ)
    (q : Fin (k + 1) → Fin (n.len + 1) → ι) :
    ((Arrow.mk f).cechNerve.obj (op n)).presheaf.obj
        (op (cechOpenIntersection (schemeCechTupleOpen f U (op n)) (cechTupleSupport q))) ≅
      Scheme.Γ.obj (op (finiteFamilyCechComponent
        (fun a : Fin (k + 1) → ι ↦ (⨅ r, U (a r)).ι ≫ f) n (fun j r ↦ q r j))) :=
  ((Arrow.mk f).cechNerve.obj (op n)).presheaf.mapIso
    (eqToIso (congrArg op (schemeCechTupleIntersection_rectangular f U n k q))) ≪≫
    openFamilyCechSectionsIso f (fun a : Fin (k + 1) → ι ↦ ⨅ r, U (a r)) n (fun j r ↦ q r j)

set_option backward.isDefEq.respectTransparency false in
/-- 元の交叉上への増大は、同じ矩形の混合積の基底の Γ へ移る。 -/
theorem rectangularCechSectionsIso_augmentation (n : SimplexCategory) (k : ℕ)
    (q : Fin (k + 1) → Fin (n.len + 1) → ι) :
    (WidePullback.base (fun _ : Fin (n.len + 1) ↦ f)).appLE ⊤
        (cechOpenIntersection (schemeCechTupleOpen f U (op n)) (cechTupleSupport q)) (by simp) ≫
        (rectangularCechSectionsIso f U n k q).hom =
      Scheme.Γ.map (WidePullback.base
        (fun j : Fin (n.len + 1) ↦ (⨅ r : Fin (k + 1), U (q r j)).ι ≫ f)).op := by
  let v := WidePullback.base (fun _ : Fin (n.len + 1) ↦ f)
  let O := cechOpenIntersection (schemeCechTupleOpen f U (op n)) (cechTupleSupport q)
  let V := schemeCechTupleOpen f (fun a : Fin (k + 1) → ι ↦ ⨅ r, U (a r))
    (op n) (fun j r ↦ q r j)
  let hh : O ≤ v ⁻¹ᵁ ⊤ := by simp
  have hv := Scheme.Hom.appLE_map v hh
    (eqToHom (congrArg op (schemeCechTupleIntersection_rectangular f U n k q)))
  have he := congrArg (fun w ↦ w ≫
    (openFamilyCechSectionsIso f (fun a : Fin (k + 1) → ι ↦ ⨅ r, U (a r))
      n (fun j r ↦ q r j)).hom) hv
  have hAug := openFamilyCechSectionsIso_augmentation f
    (fun a : Fin (k + 1) → ι ↦ ⨅ r, U (a r)) n (fun j r ↦ q r j)
  change v.appLE ⊤ O hh ≫
      (((Arrow.mk f).cechNerve.obj (op n)).presheaf.map
        (eqToHom (congrArg op (schemeCechTupleIntersection_rectangular f U n k q))) ≫
        (openFamilyCechSectionsIso f (fun a : Fin (k + 1) → ι ↦ ⨅ r, U (a r))
          n (fun j r ↦ q r j)).hom) = _
  exact (Category.assoc _ _ _).symm.trans (he.trans hAug)

/-- 元の nerve の射は、同じ有限像の交叉による矩形の開を保つ。 -/
theorem rectangularCechMap_le {m n : SimplexCategory} (a : m ⟶ n) (k : ℕ)
    (q : Fin (k + 1) → Fin (n.len + 1) → ι) :
    cechOpenIntersection (schemeCechTupleOpen f U (op n)) (cechTupleSupport q) ≤
      (Arrow.mk f).cechNerve.map a.op ⁻¹ᵁ
        cechOpenIntersection (schemeCechTupleOpen f U (op m))
          (cechTupleSupport (fun r j ↦ q r (a.toOrderHom j))) := by
  rw [schemeCechTupleIntersection_rectangular, schemeCechTupleIntersection_rectangular]
  exact schemeCechTupleOpen_map_le f
    (fun v : Fin (k + 1) → ι ↦ ⨅ r, U (v r)) a.op (fun j r ↦ q r j)

set_option backward.isDefEq.respectTransparency false in
/-- 同じ矩形の係数比較は、元の交叉上の appLE と全ての単体の射に自然。 -/
theorem rectangularCechSectionsIso_naturality {m n : SimplexCategory} (a : m ⟶ n) (k : ℕ)
    (q : Fin (k + 1) → Fin (n.len + 1) → ι) :
    ((Arrow.mk f).cechNerve.map a.op).appLE
        (cechOpenIntersection (schemeCechTupleOpen f U (op m))
          (cechTupleSupport (fun r j ↦ q r (a.toOrderHom j))))
        (cechOpenIntersection (schemeCechTupleOpen f U (op n)) (cechTupleSupport q))
        (rectangularCechMap_le f U a k q) ≫ (rectangularCechSectionsIso f U n k q).hom =
      (rectangularCechSectionsIso f U m k (fun r j ↦ q r (a.toOrderHom j))).hom ≫
        Scheme.Γ.map (finiteFamilyCechComponentMap
          (fun v : Fin (k + 1) → ι ↦ (⨅ r, U (v r)).ι ≫ f) a (fun j r ↦ q r j)).op := by
  simp only [rectangularCechSectionsIso, Iso.trans_hom, Functor.mapIso_hom, eqToIso]
  rw [← Category.assoc, Scheme.Hom.appLE_map]
  have he := congrArg (fun v ↦
    ((Arrow.mk f).cechNerve.obj (op m)).presheaf.map
      (eqToHom (congrArg op (schemeCechTupleIntersection_rectangular f U m k
        (fun r j ↦ q r (a.toOrderHom j))))) ≫ v)
    (openFamilyCechSectionsIso_naturality f
      (fun v : Fin (k + 1) → ι ↦ ⨅ r, U (v r)) a (fun j r ↦ q r j))
  rw [← Category.assoc, Scheme.Hom.map_appLE] at he
  simpa only [Category.assoc] using he

end SerrePositivity.AlgebraicGeometry
