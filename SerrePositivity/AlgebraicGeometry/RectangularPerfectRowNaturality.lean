module

public import SerrePositivity.AlgebraicGeometry.RectangularPerfectRowEquiv
public import SerrePositivity.AlgebraicGeometry.FrobeniusDirectLimitRingIsoNaturality

/-!
概要：元の矩形の行の係数同型は、同じ水平の全ての射に自然である。
方針：各成分の標準同型に戻し、有限族と元の appLE の自然性を合成する。
規約：元の交叉族の余積射と矩形の実際の制限を保持する。
使われ方：実際の行の交代微分を保つ完全性の移送。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
universe u
variable {Y S : Scheme.{u}} (f : Y ⟶ S) {ι : Type} [Fintype ι] [DecidableEq ι]
variable (U : ι → Y.Opens) (p : ℕ) (hp : p.Prime)

set_option backward.isDefEq.respectTransparency false in
/-- 同じ行の係数同型は、元の余積射の nerve と実際の矩形の appLE に自然。 -/
theorem rectangularPerfectRowEquiv_naturality {m n : SimplexCategory} (a : m ⟶ n) (k : ℕ)
    (hM : (p : Scheme.Γ.obj (op ((Arrow.mk (Sigma.desc
      (fun b : Fin (k + 1) → ι ↦ (⨅ r, U (b r)).ι ≫ f))).cechNerve.obj (op m)))) = 0)
    (hN : (p : Scheme.Γ.obj (op ((Arrow.mk (Sigma.desc
      (fun b : Fin (k + 1) → ι ↦ (⨅ r, U (b r)).ι ≫ f))).cechNerve.obj (op n)))) = 0)
    (hPM : ∀ q : Fin (k + 1) → Fin (m.len + 1) → ι,
      (p : ((Arrow.mk f).cechNerve.obj (op m)).presheaf.obj
        (op (cechOpenIntersection (schemeCechTupleOpen f U (op m)) (cechTupleSupport q)))) = 0)
    (hPN : ∀ q : Fin (k + 1) → Fin (n.len + 1) → ι,
      (p : ((Arrow.mk f).cechNerve.obj (op n)).presheaf.obj
        (op (cechOpenIntersection (schemeCechTupleOpen f U (op n)) (cechTupleSupport q)))) = 0)
    (z : FrobeniusDirectLimit (Scheme.Γ.obj (op ((Arrow.mk (Sigma.desc
      (fun b : Fin (k + 1) → ι ↦ (⨅ r, U (b r)).ι ≫ f))).cechNerve.obj (op m)))) p hp hM)
    (q : Fin (k + 1) → Fin (n.len + 1) → ι) :
    rectangularPerfectRowEquiv f U p hp n k hN hPN
        (frobeniusDirectLimitMap p hp hM hN
          (Scheme.Γ.map ((Arrow.mk (Sigma.desc
            (fun b : Fin (k + 1) → ι ↦ (⨅ r, U (b r)).ι ≫ f))).cechNerve.map a.op).op).hom z) q =
      frobeniusDirectLimitMap p hp (hPM (fun r j ↦ q r (a.toOrderHom j))) (hPN q)
        (((Arrow.mk f).cechNerve.map a.op).appLE
          (cechOpenIntersection (schemeCechTupleOpen f U (op m))
            (cechTupleSupport (fun r j ↦ q r (a.toOrderHom j))))
          (cechOpenIntersection (schemeCechTupleOpen f U (op n)) (cechTupleSupport q))
          (rectangularCechMap_le f U a k q)).hom
        (rectangularPerfectRowEquiv f U p hp m k hM hPM z (fun r j ↦ q r (a.toOrderHom j))) := by
  let g := fun b : Fin (k + 1) → ι ↦ (⨅ r, U (b r)).ι ≫ f
  let Q := fun r j ↦ q r (a.toOrderHom j)
  let T := fun j r ↦ q r j
  let cM := finiteFamilyCechComponent_primeCast g p m hM (fun j r ↦ Q r j)
  let cN := finiteFamilyCechComponent_primeCast g p n hN T
  let eN := frobeniusDirectLimitRingIso p hp (hPN q) cN (rectangularCechSectionsIso f U n k q)
  apply eN.injective
  have hn := rectangularPerfectRowEquiv_apply f U p hp n k hN hPN
    (frobeniusDirectLimitMap p hp hM hN
      (Scheme.Γ.map ((Arrow.mk (Sigma.desc g)).cechNerve.map a.op).op).hom z) q
  have hm := rectangularPerfectRowEquiv_apply f U p hp m k hM hPM z Q
  have hf := finiteFamilyCechFrobeniusEquiv_naturality g p hp a hM hN z T
  have hr := frobeniusDirectLimitRingIso_naturality p hp (hPM Q) cM (hPN q) cN
    (rectangularCechSectionsIso f U m k Q) (rectangularCechSectionsIso f U n k q)
    (((Arrow.mk f).cechNerve.map a.op).appLE
      (cechOpenIntersection (schemeCechTupleOpen f U (op m)) (cechTupleSupport Q))
      (cechOpenIntersection (schemeCechTupleOpen f U (op n)) (cechTupleSupport q))
      (rectangularCechMap_le f U a k q)).hom
    (Scheme.Γ.map (finiteFamilyCechComponentMap g a T).op).hom
    (rectangularCechSectionsIso_naturality f U a k q)
    (rectangularPerfectRowEquiv f U p hp m k hM hPM z Q)
  exact hn.trans (hf.trans ((congrArg
    (frobeniusDirectLimitMap p hp cM cN
      (Scheme.Γ.map (finiteFamilyCechComponentMap g a T).op).hom) hm.symm).trans hr.symm))

end SerrePositivity.AlgebraicGeometry
