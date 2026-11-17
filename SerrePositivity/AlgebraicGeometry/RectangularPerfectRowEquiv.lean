module

public import SerrePositivity.AlgebraicGeometry.RectangularCechCoefficients
public import SerrePositivity.AlgebraicGeometry.FiniteFamilyCechFrobenius

/-!
概要：同じ交叉族の余積射の係数を、元の二重 Čech の矩形の係数の積へ移す。
方針：有限族の係数比較、同じ行列の転置、元の切断環の同型を合成する。
規約：元の有限交叉と全ての成分の写像を保持する。
使われ方：実際の二重 Čech の行への完全性の移送。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
universe u
variable {Y S : Scheme.{u}} (f : Y ⟶ S) {ι : Type} [Fintype ι] [DecidableEq ι]
variable (U : ι → Y.Opens) (p : ℕ) (hp : p.Prime)

/-- 同じ余積射の係数を、元の矩形タプルの実際の係数の積へ移す標準環同型。 -/
def rectangularPerfectRowEquiv (n : SimplexCategory) (k : ℕ)
    (hN : (p : Scheme.Γ.obj (op ((Arrow.mk (Sigma.desc
      (fun a : Fin (k + 1) → ι ↦ (⨅ r, U (a r)).ι ≫ f))).cechNerve.obj (op n)))) = 0)
    (hP : ∀ q : Fin (k + 1) → Fin (n.len + 1) → ι,
      (p : ((Arrow.mk f).cechNerve.obj (op n)).presheaf.obj
        (op (cechOpenIntersection (schemeCechTupleOpen f U (op n)) (cechTupleSupport q)))) = 0) :
    FrobeniusDirectLimit (Scheme.Γ.obj (op ((Arrow.mk (Sigma.desc
        (fun a : Fin (k + 1) → ι ↦ (⨅ r, U (a r)).ι ≫ f))).cechNerve.obj (op n)))) p hp hN ≃+*
      ∀ q : Fin (k + 1) → Fin (n.len + 1) → ι,
        FrobeniusDirectLimit (((Arrow.mk f).cechNerve.obj (op n)).presheaf.obj
          (op (cechOpenIntersection (schemeCechTupleOpen f U (op n)) (cechTupleSupport q))))
            p hp (hP q) := by
  let g := fun a : Fin (k + 1) → ι ↦ (⨅ r, U (a r)).ι ≫ f
  let A := fun t : Fin (n.len + 1) → Fin (k + 1) → ι ↦
    FrobeniusDirectLimit (Scheme.Γ.obj (op (finiteFamilyCechComponent g n t)))
      p hp (finiteFamilyCechComponent_primeCast g p n hN t)
  let e := Equiv.piComm (fun (_ : Fin (n.len + 1)) (_ : Fin (k + 1)) ↦ ι)
  exact (finiteFamilyCechFrobeniusEquiv g p hp n hN).trans
    ((RingEquiv.piCongrLeft' A e).trans (RingEquiv.piCongrRight (fun q ↦
      (frobeniusDirectLimitRingIso p hp (hP q)
        (finiteFamilyCechComponent_primeCast g p n hN (fun j r ↦ q r j))
        (rectangularCechSectionsIso f U n k q)).symm)))

set_option backward.isDefEq.respectTransparency false in
/-- 同じ行の係数比較を有限段で評価すると、元の入射と同じ切断環の逆同型を使う。 -/
theorem rectangularPerfectRowEquiv_of (n : SimplexCategory) (k : ℕ)
    (hN : (p : Scheme.Γ.obj (op ((Arrow.mk (Sigma.desc
      (fun a : Fin (k + 1) → ι ↦ (⨅ r, U (a r)).ι ≫ f))).cechNerve.obj (op n)))) = 0)
    (hP : ∀ q : Fin (k + 1) → Fin (n.len + 1) → ι,
      (p : ((Arrow.mk f).cechNerve.obj (op n)).presheaf.obj
        (op (cechOpenIntersection (schemeCechTupleOpen f U (op n)) (cechTupleSupport q)))) = 0)
    (s : ℕ) (x : Scheme.Γ.obj (op ((Arrow.mk (Sigma.desc
      (fun a : Fin (k + 1) → ι ↦ (⨅ r, U (a r)).ι ≫ f))).cechNerve.obj (op n))))
    (q : Fin (k + 1) → Fin (n.len + 1) → ι) :
    rectangularPerfectRowEquiv f U p hp n k hN hP (frobeniusDirectLimitOf _ p hp hN s x) q =
      frobeniusDirectLimitOf _ p hp (hP q) s
        ((rectangularCechSectionsIso f U n k q).inv.hom
          ((Scheme.Γ.map (finiteFamilyCechInclusion
            (fun a : Fin (k + 1) → ι ↦ (⨅ r, U (a r)).ι ≫ f) n (fun j r ↦ q r j)).op).hom x)) := by
  let g := fun a : Fin (k + 1) → ι ↦ (⨅ r, U (a r)).ι ≫ f
  change frobeniusDirectLimitMap p hp
      (finiteFamilyCechComponent_primeCast g p n hN (fun j r ↦ q r j)) (hP q)
      (rectangularCechSectionsIso f U n k q).inv.hom
      (finiteFamilyCechFrobeniusEquiv g p hp n hN (frobeniusDirectLimitOf _ p hp hN s x)
        (fun j r ↦ q r j)) = _
  rw [finiteFamilyCechFrobeniusEquiv_of, frobeniusDirectLimitMap_of]

set_option backward.isDefEq.respectTransparency false in
/-- 元の矩形の切断環の標準比較に戻すと、同じ転置した成分の評価になる。 -/
theorem rectangularPerfectRowEquiv_apply (n : SimplexCategory) (k : ℕ)
    (hN : (p : Scheme.Γ.obj (op ((Arrow.mk (Sigma.desc
      (fun a : Fin (k + 1) → ι ↦ (⨅ r, U (a r)).ι ≫ f))).cechNerve.obj (op n)))) = 0)
    (hP : ∀ q : Fin (k + 1) → Fin (n.len + 1) → ι,
      (p : ((Arrow.mk f).cechNerve.obj (op n)).presheaf.obj
        (op (cechOpenIntersection (schemeCechTupleOpen f U (op n)) (cechTupleSupport q)))) = 0)
    (z : FrobeniusDirectLimit (Scheme.Γ.obj (op ((Arrow.mk (Sigma.desc
      (fun a : Fin (k + 1) → ι ↦ (⨅ r, U (a r)).ι ≫ f))).cechNerve.obj (op n)))) p hp hN)
    (q : Fin (k + 1) → Fin (n.len + 1) → ι) :
    frobeniusDirectLimitRingIso p hp (hP q)
        (finiteFamilyCechComponent_primeCast
          (fun a : Fin (k + 1) → ι ↦ (⨅ r, U (a r)).ι ≫ f) p n hN (fun j r ↦ q r j))
        (rectangularCechSectionsIso f U n k q)
        (rectangularPerfectRowEquiv f U p hp n k hN hP z q) =
      finiteFamilyCechFrobeniusEquiv
        (fun a : Fin (k + 1) → ι ↦ (⨅ r, U (a r)).ι ≫ f) p hp n hN z
        (fun j r ↦ q r j) := by
  let e := frobeniusDirectLimitRingIso p hp (hP q)
    (finiteFamilyCechComponent_primeCast
      (fun a : Fin (k + 1) → ι ↦ (⨅ r, U (a r)).ι ≫ f) p n hN (fun j r ↦ q r j))
    (rectangularCechSectionsIso f U n k q)
  change e (e.symm _) = _
  exact e.apply_symm_apply _

end SerrePositivity.AlgebraicGeometry
