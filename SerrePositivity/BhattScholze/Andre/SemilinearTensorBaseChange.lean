module

public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# André E1・E2：係数環同型に沿う半線形同型の実底変換

## 概要

係数環同型に沿う半線形環同型は、通常テンソル底変換の代数同型を与える。
BS Rem 7.15（著者版 p.62）の Frobenius 引戻しを実際のテンソルで記述する準備。

## 方針

順射はテンソル積の普遍性、逆射は右因子への標準射と逆環同型の合成で構成する。

## 規約

通常の可換環テンソル積を使う。正則性・平坦性・標数の仮定は不要。

## 使われ方

逆 Frobenius 係数入力の表示を元の多項式の表示へ実底変換する。
-/

@[expose] public noncomputable section
universe u v w z
namespace SerrePositivity.BhattScholze.Andre
open scoped TensorProduct
variable {R : Type u} {S : Type v} {B : Type w} {C : Type z}
variable [CommRing R] [CommRing S] [CommRing B] [CommRing C]
variable [Algebra R B] [Algebra S C]

/-- 概要：半線形環同型は実テンソル底変換の代数同型を誘導する。
方針：順方向のテンソル普遍射と右因子への逆射を単純テンソル上で照合する。
規約：係数環同型とその係数可換性を明示する。
使われ方：BS Rem 7.15（著者版 p.62）の係数 Frobenius に沿う引戻し。 -/
def tensorBaseChangeAlgEquivOfSemilinearRingEquiv
    (e : R ≃+* S) (F : B ≃+* C)
    (hF : ∀ r : R, F (algebraMap R B r) = algebraMap S C (e r)) :
    let := e.toRingHom.toAlgebra
    S ⊗[R] B ≃ₐ[S] C := by
  let := e.toRingHom.toAlgebra
  let : Algebra R C := ((algebraMap S C).comp e.toRingHom).toAlgebra
  let : IsScalarTower R S C := IsScalarTower.of_algebraMap_eq' rfl
  let fB : B →ₐ[R] C := { F.toRingHom with commutes' := hF }
  let fS : S →ₐ[R] C := IsScalarTower.toAlgHom R S C
  let hc : ∀ s b, Commute (fS s) (fB b) := fun _ _ => Commute.all _ _
  let f := (Algebra.TensorProduct.lift fS fB hc).toRingHom
  let g := (Algebra.TensorProduct.includeRight : B →ₐ[R] S ⊗[R] B).toRingHom.comp F.symm.toRingHom
  have hfg : f.comp g = RingHom.id C := by
    apply RingHom.ext
    intro c
    change Algebra.TensorProduct.lift fS fB hc ((1 : S) ⊗ₜ[R] F.symm c) = c
    rw [Algebra.TensorProduct.lift_tmul]
    change fS 1 * F (F.symm c) = c
    rw [map_one, one_mul, RingEquiv.apply_symm_apply]
  have hgf : g.comp f = RingHom.id (S ⊗[R] B) := by
    apply RingHom.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
    | tmul s b =>
      obtain ⟨r, rfl⟩ := e.surjective s
      change (1 : S) ⊗ₜ[R] F.symm
        (Algebra.TensorProduct.lift fS fB hc ((e r) ⊗ₜ[R] b)) = (e r) ⊗ₜ[R] b
      rw [Algebra.TensorProduct.lift_tmul]
      change (1 : S) ⊗ₜ[R] F.symm (algebraMap S C (e r) * F b) = _
      rw [← hF r, ← map_mul, RingEquiv.symm_apply_apply]
      rw [← Algebra.smul_def r b]
      rw [← TensorProduct.smul_tmul r (1 : S) b]
      rw [Algebra.smul_def r (1 : S), RingHom.algebraMap_toAlgebra, mul_one]
      rfl
  refine { RingEquiv.ofRingHom f g hfg hgf with commutes' := ?_ }
  intro s
  change Algebra.TensorProduct.lift fS fB hc (s ⊗ₜ[R] (1 : B)) = algebraMap S C s
  rw [Algebra.TensorProduct.lift_tmul]
  simp only [map_one, mul_one]
  rfl

/-- 概要：実底変換同型は単純テンソルを標準係数と半線形像の積へ送る。
方針：テンソル普遍射の単純テンソル公式を使う。
規約：係数環の任意の元と元の代数の任意の元を含む。
使われ方：BS Rem 7.15（著者版 p.62）の実引戻しの標準係数を追跡する。 -/
theorem tensorBaseChangeAlgEquivOfSemilinearRingEquiv_tmul
    (e : R ≃+* S) (F : B ≃+* C)
    (hF : ∀ r : R, F (algebraMap R B r) = algebraMap S C (e r)) (s : S) (b : B) :
    let := e.toRingHom.toAlgebra
    tensorBaseChangeAlgEquivOfSemilinearRingEquiv e F hF (s ⊗ₜ[R] b) =
      algebraMap S C s * F b := by
  let := e.toRingHom.toAlgebra
  rfl

end SerrePositivity.BhattScholze.Andre
