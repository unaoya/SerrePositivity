module

public import SerrePositivity.AlgebraicGeometry.FiniteFamilyCechGamma
public import SerrePositivity.AlgebraicGeometry.FrobeniusDirectLimitRingIso
public import SerrePositivity.AlgebraicGeometry.FrobeniusDirectLimitPi

/-!
概要：同じ有限族の nerve の Frobenius 係数を、元の混合積の係数の積へ移す。
方針：元の Γ の環同型と、実際の有限積の Frobenius 比較を合成する。
規約：元の評価、単体の射、増大からの写像を保持する。
使われ方：同じ矩形タプルの二重 Čech の係数比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
universe u
variable {ι : Type} {S : Scheme.{u}} {Z : ι → Scheme.{u}} (f : ∀ i, Z i ⟶ S)
variable (p : ℕ) (hp : p.Prime)

/-- 元の標準入射の Γ により、同じ混合積の標数条件を供給する。 -/
theorem finiteFamilyCechComponent_primeCast (n : SimplexCategory)
    (hN : (p : Scheme.Γ.obj (op ((Arrow.mk (Sigma.desc f)).cechNerve.obj (op n)))) = 0)
    (t : Fin (n.len + 1) → ι) :
    (p : Scheme.Γ.obj (op (finiteFamilyCechComponent f n t))) = 0 := by
  rw [← map_natCast (Scheme.Γ.map (finiteFamilyCechInclusion f n t).op).hom, hN, map_zero]

/-- 元の有限族の同じ標準比較から得る、実際の Frobenius 係数の環同型。 -/
def finiteFamilyCechFrobeniusEquiv [Fintype ι] (n : SimplexCategory)
    (hN : (p : Scheme.Γ.obj (op ((Arrow.mk (Sigma.desc f)).cechNerve.obj (op n)))) = 0) :
    FrobeniusDirectLimit (Scheme.Γ.obj (op ((Arrow.mk (Sigma.desc f)).cechNerve.obj (op n))))
        p hp hN ≃+*
      ∀ t : Fin (n.len + 1) → ι,
        FrobeniusDirectLimit (Scheme.Γ.obj (op (finiteFamilyCechComponent f n t)))
          p hp (finiteFamilyCechComponent_primeCast f p n hN t) :=
  (frobeniusDirectLimitRingIso p hp hN
    (frobeniusPi_primeCast _ p (finiteFamilyCechComponent_primeCast f p n hN))
    (finiteFamilyCechGammaIso f n)).trans
      (frobeniusDirectLimitPiEquiv _ p hp (finiteFamilyCechComponent_primeCast f p n hN))

set_option backward.isDefEq.respectTransparency false in
/-- 同じ有限段での評価は、元の混合積の標準入射の Γ に一致する。 -/
theorem finiteFamilyCechFrobeniusEquiv_of [Fintype ι] (n : SimplexCategory)
    (hN : (p : Scheme.Γ.obj (op ((Arrow.mk (Sigma.desc f)).cechNerve.obj (op n)))) = 0)
    (k : ℕ) (x : Scheme.Γ.obj (op ((Arrow.mk (Sigma.desc f)).cechNerve.obj (op n))))
    (t : Fin (n.len + 1) → ι) :
    finiteFamilyCechFrobeniusEquiv f p hp n hN (frobeniusDirectLimitOf _ p hp hN k x) t =
      frobeniusDirectLimitOf _ p hp (finiteFamilyCechComponent_primeCast f p n hN t) k
        ((Scheme.Γ.map (finiteFamilyCechInclusion f n t).op).hom x) := by
  change frobeniusDirectLimitOf _ p hp _ k ((finiteFamilyCechGammaIso f n).hom.hom x t) = _
  exact congrArg (frobeniusDirectLimitOf _ p hp _ k)
    (congrArg (fun g : CommRingCat.Hom _ _ ↦ g.hom x) (finiteFamilyCechGammaIso_eval f n t))

set_option backward.isDefEq.respectTransparency false in
/-- 単体の射と同じタプルの再添字付けを、実際の Frobenius 係数の比較も保つ。 -/
theorem finiteFamilyCechFrobeniusEquiv_naturality [Fintype ι]
    {m n : SimplexCategory} (a : m ⟶ n)
    (hM : (p : Scheme.Γ.obj (op ((Arrow.mk (Sigma.desc f)).cechNerve.obj (op m)))) = 0)
    (hN : (p : Scheme.Γ.obj (op ((Arrow.mk (Sigma.desc f)).cechNerve.obj (op n)))) = 0)
    (z : FrobeniusDirectLimit (Scheme.Γ.obj
      (op ((Arrow.mk (Sigma.desc f)).cechNerve.obj (op m)))) p hp hM)
    (t : Fin (n.len + 1) → ι) :
    finiteFamilyCechFrobeniusEquiv f p hp n hN
        (frobeniusDirectLimitMap p hp hM hN
          (Scheme.Γ.map ((Arrow.mk (Sigma.desc f)).cechNerve.map a.op).op).hom z) t =
      frobeniusDirectLimitMap p hp
        (finiteFamilyCechComponent_primeCast f p m hM (fun j ↦ t (a.toOrderHom j)))
        (finiteFamilyCechComponent_primeCast f p n hN t)
        (Scheme.Γ.map (finiteFamilyCechComponentMap f a t).op).hom
        (finiteFamilyCechFrobeniusEquiv f p hp m hM z (fun j ↦ t (a.toOrderHom j))) := by
  obtain ⟨k, x, hx⟩ := DirectLimit.exists_eq_mk (frobeniusDirectSystemMap _ p hp hM) z
  change z = frobeniusDirectLimitOf _ p hp hM k x at hx
  rw [hx]
  rw [frobeniusDirectLimitMap_of, finiteFamilyCechFrobeniusEquiv_of,
    finiteFamilyCechFrobeniusEquiv_of, frobeniusDirectLimitMap_of]
  apply congrArg (frobeniusDirectLimitOf _ p hp _ k)
  have hc := congrArg (fun g ↦ Scheme.Γ.map g.op)
    (finiteFamilyCechInclusion_naturality f a t)
  simp only [CategoryTheory.op_comp, CategoryTheory.Functor.map_comp] at hc
  exact congrArg (fun g : CommRingCat.Hom _ _ ↦ g.hom x) hc.symm

set_option backward.isDefEq.respectTransparency false in
/-- 元の基底からの増大も、同じ成分の基底の射の Frobenius 写像へ移る。 -/
theorem finiteFamilyCechFrobeniusEquiv_augmentation [Fintype ι]
    (hS : (p : Scheme.Γ.obj (op S)) = 0) (n : SimplexCategory)
    (hN : (p : Scheme.Γ.obj (op ((Arrow.mk (Sigma.desc f)).cechNerve.obj (op n)))) = 0)
    (z : FrobeniusDirectLimit (Scheme.Γ.obj (op S)) p hp hS)
    (t : Fin (n.len + 1) → ι) :
    finiteFamilyCechFrobeniusEquiv f p hp n hN
        (frobeniusDirectLimitMap p hp hS hN
          (Scheme.Γ.map (WidePullback.base
            (fun _ : Fin (n.len + 1) ↦ Sigma.desc f)).op).hom z) t =
      frobeniusDirectLimitMap p hp hS (finiteFamilyCechComponent_primeCast f p n hN t)
        (Scheme.Γ.map (WidePullback.base (fun j ↦ f (t j))).op).hom z := by
  obtain ⟨k, x, hx⟩ := DirectLimit.exists_eq_mk (frobeniusDirectSystemMap _ p hp hS) z
  change z = frobeniusDirectLimitOf _ p hp hS k x at hx
  rw [hx]
  rw [frobeniusDirectLimitMap_of, finiteFamilyCechFrobeniusEquiv_of,
    frobeniusDirectLimitMap_of]
  apply congrArg (frobeniusDirectLimitOf _ p hp _ k)
  have hc := congrArg (fun g ↦ Scheme.Γ.map g.op) (finiteFamilyCechInclusion_base f n t)
  simp only [CategoryTheory.op_comp, CategoryTheory.Functor.map_comp] at hc
  exact congrArg (fun g : CommRingCat.Hom _ _ ↦ g.hom x) hc

end SerrePositivity.AlgebraicGeometry
