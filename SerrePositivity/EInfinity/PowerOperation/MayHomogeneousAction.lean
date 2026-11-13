module

public import SerrePositivity.EInfinity.PowerOperation.MayResolutionCoordinates
public import SerrePositivity.EInfinity.PowerOperation.MayRepeatedCycles

/-!
# May の係数と同次入力に対する BE の作用

May, Definition 2.1 の θ(e_i ⊗ a^{⊗p}) を元の BE の作用で評価する前段。
ここでは任意の同次係数と入力について微分と厳密代数射の自然性を計算する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
open SerrePositivity.EInfinity.BarrattEccles
variable {k : Type u} [CommRing k] (X : (operad k).Algebra)

/-- BE の指定作用を全複体の同次純テンソルに評価する。 -/
def mayHomogeneousAction (p : ℕ) (r q : ℤ)
    (c : ((operad k).arity p).X r) (y : (power X.carrier p).X q) :
    X.carrier.X (r + q) :=
  (X.action p).f (r + q)
    (ιTensorObj ((operad k).arity p) (power X.carrier p) r q (r + q) rfl (c ⊗ₜ[k] y))

/-- May の同次作用の微分は、係数微分と Koszul 符号付きの入力微分。 -/
lemma mayHomogeneousAction_d (p : ℕ) (r q : ℤ)
    (c : ((operad k).arity p).X r) (y : (power X.carrier p).X q) :
    X.carrier.d (r + q) (r + q + 1) (mayHomogeneousAction X p r q c y) =
      (X.action p).f (r + q + 1)
        (ιTensorObj ((operad k).arity p) (power X.carrier p) (r + 1) q (r + q + 1)
            (by omega) (((operad k).arity p).d r (r + 1) c ⊗ₜ[k] y)) +
      r.negOnePow • (X.action p).f (r + q + 1)
        (ιTensorObj ((operad k).arity p) (power X.carrier p) r (q + 1) (r + q + 1)
            (by omega) (c ⊗ₜ[k] (power X.carrier p).d q (q + 1) y)) := by
  have hc := congrArg (fun f => f
    (ιTensorObj ((operad k).arity p) (power X.carrier p) r q (r + q) rfl (c ⊗ₜ[k] y)))
    ((X.action p).comm (r + q) (r + q + 1))
  change X.carrier.d (r + q) (r + q + 1) ((X.action p).f (r + q) _) =
    (X.action p).f (r + q + 1)
      ((cochainTensor ((operad k).arity p) (power X.carrier p)).d _ _ _) at hc
  rw [mayHomogeneousAction, hc, cochainTensor_d_apply_ι]
  change ((X.action p).f (r + q + 1)).hom (_ + _) = _
  simp only [map_add, Units.smul_def, map_zsmul]

/-- 同じ係数を使う同次作用は、全厳密 BE 射に自然。 -/
lemma mayHomogeneousAction_naturality {Y : (operad k).Algebra} (f : X ⟶ Y)
    (p : ℕ) (r q : ℤ) (c : ((operad k).arity p).X r)
    (y : (power X.carrier p).X q) :
    f.hom.f (r + q) (mayHomogeneousAction X p r q c y) =
      mayHomogeneousAction Y p r q c ((TensorPowers.map f.hom p).f q y) := by
  have hc := congrArg (fun g => g.f (r + q)) (f.comm p)
  have he := congrArg (fun g => g
    (ιTensorObj ((operad k).arity p) (power X.carrier p) r q (r + q) rfl (c ⊗ₜ[k] y))) hc
  change f.hom.f (r + q) ((X.action p).f (r + q) _) =
    (Y.action p).f (r + q)
      ((cochainTensorMap (𝟙 _) (TensorPowers.map f.hom p)).f _ _) at he
  rw [mayHomogeneousAction, he]
  change (Y.action p).f _ ((cochainTensorMap (𝟙 _) (TensorPowers.map f.hom p)).f _ _) = _
  rw [cochainTensorMap_apply_ι]
  rfl

/-- 同次作用の二変数線形性。 -/
def mayHomogeneousActionLinear (p : ℕ) (r q : ℤ) :
    ((operad k).arity p).X r →ₗ[k] (power X.carrier p).X q →ₗ[k]
      X.carrier.X (r + q) :=
  TensorProduct.curry (((X.action p).f (r + q)).hom.comp
    (ιTensorObj ((operad k).arity p) (power X.carrier p) r q (r + q) rfl).hom)

lemma mayHomogeneousActionLinear_apply (p : ℕ) (r q : ℤ)
    (c : ((operad k).arity p).X r) (y : (power X.carrier p).X q) :
    mayHomogeneousActionLinear X p r q c y = mayHomogeneousAction X p r q c y := rfl

/-- 係数と入力を同時に置換しても同じ元になる、元の圏での等変性。 -/
lemma mayHomogeneousAction_equivariance (p : ℕ) (σ : Equiv.Perm (Fin p)) (r q : ℤ)
    (c : ((operad k).arity p).X r) (y : (power X.carrier p).X q) :
    mayHomogeneousAction X p r q
      (((operad k).sequence.map (FiniteBijection.permutation p σ)).f r c)
      ((permutationAction X.carrier p σ).asIso.hom.f q y) =
        mayHomogeneousAction X p r q c y := by
  have hc := congrArg (fun f => f.f (r + q)) (X.equivariance p σ)
  have he := congrArg (fun f => f
    (ιTensorObj ((operad k).arity p) (power X.carrier p) r q (r + q) rfl (c ⊗ₜ[k] y))) hc
  change (X.action p).f (r + q)
    ((cochainTensorMap ((operad k).sequence.map (FiniteBijection.permutation p σ))
      (permutationAction X.carrier p σ).asIso.hom).f _ _) = _ at he
  have hm := cochainTensorMap_apply_ι
    ((operad k).sequence.map (FiniteBijection.permutation p σ))
    (permutationAction X.carrier p σ).asIso.hom r q (r + q) rfl c y
  exact (congrArg (fun z => (X.action p).f (r + q) z) hm).symm.trans he

/-- 同次作用が零であることを、全次数の別の式へ移す。 -/
lemma mayHomogeneousAction_zero_at (p : ℕ) (r q t : ℤ) (h : r + q = t)
    (c : ((operad k).arity p).X r) (y : (power X.carrier p).X q)
    (hz : mayHomogeneousAction X p r q c y = 0) :
    (X.action p).f t
      (ιTensorObj ((operad k).arity p) (power X.carrier p) r q t h (c ⊗ₜ[k] y)) = 0 := by
  subst t
  exact hz

/-- 閉入力と、作用後に消える係数境界から閉じた作用値を得る。 -/
lemma mayHomogeneousAction_cycle (p : ℕ) (r q : ℤ)
    (c : ((operad k).arity p).X r) (y : (power X.carrier p).X q)
    (hy : (power X.carrier p).d q (q + 1) y = 0)
    (hc : mayHomogeneousAction X p (r + 1) q
      (((operad k).arity p).d r (r + 1) c) y = 0) :
    X.carrier.d (r + q) (r + q + 1) (mayHomogeneousAction X p r q c y) = 0 := by
  have hz : mayHomogeneousAction X p r (q + 1) c 0 = 0 :=
    (mayHomogeneousActionLinear X p r (q + 1) c).map_zero
  rw [mayHomogeneousAction_d, hy,
    mayHomogeneousAction_zero_at X p (r + 1) q _ (by omega) _ y hc,
    mayHomogeneousAction_zero_at X p r (q + 1) _ (by omega) c 0 hz,
    smul_zero, add_zero]

end SerrePositivity.EInfinity.PowerOperation
