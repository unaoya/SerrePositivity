module

public import SerrePositivity.AlgebraicGeometry.RectangularPerfectRowEquiv
public import SerrePositivity.AlgebraicGeometry.FrobeniusDirectLimitRingIsoNaturality

/-!
概要：元の矩形の行の係数同型は、同じ基底からの実際の増大を保つ。
方針：各成分の標準同型へ戻し、有限族と元の構造層の増大の式を使う。
規約：元の基底と同じ appLE・切断の写像を保持する。
使われ方：実際の二重 Čech の行の増大を含む完全性の移送。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
universe u
variable {Y S : Scheme.{u}} (f : Y ⟶ S) {ι : Type} [Fintype ι] [DecidableEq ι]
variable (U : ι → Y.Opens) (p : ℕ) (hp : p.Prime)

set_option backward.isDefEq.respectTransparency false in
/-- 同じ行の標準比較は、元の基底からの増大を元の矩形のappLEへ送る。 -/
theorem rectangularPerfectRowEquiv_augmentation
    (hS : (p : Scheme.Γ.obj (op S)) = 0) (n : SimplexCategory) (k : ℕ)
    (hN : (p : Scheme.Γ.obj (op ((Arrow.mk (Sigma.desc
      (fun b : Fin (k + 1) → ι ↦ (⨅ r, U (b r)).ι ≫ f))).cechNerve.obj (op n)))) = 0)
    (hP : ∀ q : Fin (k + 1) → Fin (n.len + 1) → ι,
      (p : ((Arrow.mk f).cechNerve.obj (op n)).presheaf.obj
        (op (cechOpenIntersection (schemeCechTupleOpen f U (op n)) (cechTupleSupport q)))) = 0)
    (z : FrobeniusDirectLimit (Scheme.Γ.obj (op S)) p hp hS)
    (q : Fin (k + 1) → Fin (n.len + 1) → ι) :
    rectangularPerfectRowEquiv f U p hp n k hN hP
        (frobeniusDirectLimitMap p hp hS hN
          (Scheme.Γ.map (WidePullback.base
            (fun _ : Fin (n.len + 1) ↦ Sigma.desc
              (fun b : Fin (k + 1) → ι ↦ (⨅ r, U (b r)).ι ≫ f))).op).hom z) q =
      frobeniusDirectLimitMap p hp hS (hP q)
        ((WidePullback.base (fun _ : Fin (n.len + 1) ↦ f)).appLE ⊤
          (cechOpenIntersection (schemeCechTupleOpen f U (op n)) (cechTupleSupport q))
          (by simp)).hom z := by
  let g := fun b : Fin (k + 1) → ι ↦ (⨅ r, U (b r)).ι ≫ f
  let T := fun j r ↦ q r j
  let cN := finiteFamilyCechComponent_primeCast g p n hN T
  let eN := frobeniusDirectLimitRingIso p hp (hP q) cN (rectangularCechSectionsIso f U n k q)
  apply eN.injective
  have hn := rectangularPerfectRowEquiv_apply f U p hp n k hN hP
    (frobeniusDirectLimitMap p hp hS hN
      (Scheme.Γ.map (WidePullback.base (fun _ : Fin (n.len + 1) ↦ Sigma.desc g)).op).hom z) q
  have hf := finiteFamilyCechFrobeniusEquiv_augmentation g p hp hS n hN z T
  have hr := frobeniusDirectLimitRingIso_naturality p hp hS hS (hP q) cN
    (Iso.refl (Scheme.Γ.obj (op S))) (rectangularCechSectionsIso f U n k q)
    ((WidePullback.base (fun _ : Fin (n.len + 1) ↦ f)).appLE ⊤
      (cechOpenIntersection (schemeCechTupleOpen f U (op n)) (cechTupleSupport q)) (by simp)).hom
    (Scheme.Γ.map (WidePullback.base (fun j ↦ (⨅ r : Fin (k + 1), U (q r j)).ι ≫ f)).op).hom
    (by
      change ((WidePullback.base (fun _ : Fin (n.len + 1) ↦ f)).appLE ⊤
        (cechOpenIntersection (schemeCechTupleOpen f U (op n)) (cechTupleSupport q))
        (by simp)) ≫ (rectangularCechSectionsIso f U n k q).hom = _
      exact rectangularCechSectionsIso_augmentation f U n k q) z
  change eN (frobeniusDirectLimitMap p hp hS (hP q)
      ((WidePullback.base (fun _ : Fin (n.len + 1) ↦ f)).appLE ⊤
        (cechOpenIntersection (schemeCechTupleOpen f U (op n)) (cechTupleSupport q)) (by simp)).hom z) =
    frobeniusDirectLimitMap p hp hS cN
      (Scheme.Γ.map (WidePullback.base (fun j ↦ (⨅ r : Fin (k + 1), U (q r j)).ι ≫ f)).op).hom
      (frobeniusDirectLimitMap p hp hS hS (RingHom.id _) z) at hr
  rw [frobeniusDirectLimitMap_id] at hr
  exact hn.trans (hf.trans hr.symm)

end SerrePositivity.AlgebraicGeometry
