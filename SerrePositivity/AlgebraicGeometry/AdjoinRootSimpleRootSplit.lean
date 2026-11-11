module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Etale.StandardEtale

/-!
概要：モニック多項式の単純根に対応する階数一の因子を切り出す。
方針：一次因子と残りの因子が互いに素であることを示し、中国剰余定理を適用する。
規約：単純根では微分の値が単元であると仮定する。
使われ方：標準 étale 代数を基底変更したときの対角因子。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open Polynomial

private def adjoinRootLinearEquiv {B : Type*} [CommRing B] (x : B) :
    AdjoinRoot (X - C x) ≃ₐ[B] B := by
  let e := AdjoinRoot.liftAlgHom (X - C x) (AlgHom.id B B) x (by simp)
  apply AlgEquiv.ofBijective e
  constructor
  · rw [injective_iff_map_eq_zero]
    intro a ha
    induction a using AdjoinRoot.induction_on with
    | ih p =>
      apply AdjoinRoot.mk_eq_zero.mpr
      apply dvd_iff_isRoot.mpr
      simpa [e, IsRoot, eval₂_at_apply] using ha
  · intro a
    exact ⟨algebraMap B _ a, e.commutes a⟩

/--
概要：単純根を持つモニック多項式の根を添加した代数は、基底環とモニックな残因子の
根を添加した代数との直積に分かれる。第一射影は指定根での評価。
方針：一次因子を除き、残因子の指定根での値を微分の値と比較する。
規約：残因子が定数の場合も含む。
使われ方：Stacks 0813 の標準 étale 対角の分離。
-/
theorem exists_adjoinRoot_split_of_isUnit_derivative_eval
    {B : Type*} [CommRing B] (f : B[X]) (hf : f.Monic) (x : B)
    (hx : f.eval x = 0) (hunit : IsUnit (f.derivative.eval x)) :
    ∃ g : B[X], g.Monic ∧ f = (X - C x) * g ∧
      ∃ e : AdjoinRoot f ≃ₐ[B] B × AdjoinRoot g, (e (AdjoinRoot.root f)).1 = x := by
  obtain ⟨g, hfg⟩ := dvd_iff_isRoot.mpr (show IsRoot f x from hx)
  have hg : g.Monic := (monic_X_sub_C x).of_mul_monic_left (hfg ▸ hf)
  have heval : f.derivative.eval x = g.eval x := by
    rw [hfg, derivative_mul]
    simp
  rw [heval] at hunit
  obtain ⟨u, hu⟩ := hunit
  have hmod := modByMonic_add_div g (X - C x)
  rw [modByMonic_X_sub_C_eq_C_eval] at hmod
  have hsub : g - (X - C x) * (g /ₘ (X - C x)) = C (g.eval x) :=
    (eq_sub_of_add_eq hmod).symm
  have hcop : IsCoprime (X - C x) g := by
    refine ⟨-(C (↑u⁻¹ : B) * (g /ₘ (X - C x))), C (↑u⁻¹ : B), ?_⟩
    calc
      _ = C (↑u⁻¹ : B) * (g - (X - C x) * (g /ₘ (X - C x))) := by ring
      _ = 1 := by
        rw [hsub, ← hu, ← C_mul]
        simp
  let I : Ideal B[X] := Ideal.span {X - C x}
  let J : Ideal B[X] := Ideal.span {g}
  have hij : IsCoprime I J := (Ideal.isCoprime_span_singleton_iff _ _).mpr hcop
  have hIJ : Ideal.span {f} = I * J := by
    rw [hfg, Ideal.span_singleton_mul_span_singleton]
  let e₀ := (Ideal.quotEquivOfEq hIJ).trans (Ideal.quotientMulEquivQuotientProd I J hij)
  let e₁ : AdjoinRoot f ≃ₐ[B] AdjoinRoot (X - C x) × AdjoinRoot g :=
    { __ := e₀
      commutes' := fun b => by
        change e₀ (Ideal.Quotient.mk _ (C b)) =
          (Ideal.Quotient.mk I (C b), Ideal.Quotient.mk J (C b))
        rfl }
  refine ⟨g, hg, hfg, e₁.trans (AlgEquiv.prodCongr (adjoinRootLinearEquiv x) (.refl)), ?_⟩
  change AdjoinRoot.liftAlgHom (X - C x) (AlgHom.id B B) x (by simp)
    (AdjoinRoot.root (X - C x)) = x
  exact AdjoinRoot.liftAlgHom_root _ _ _ _

open scoped TensorProduct

/--
概要：標準 étale 代数へモニック多項式の根添加を底変換すると、
対角の根を与える階数一因子と、別のモニック多項式の根添加との直積になる。
方針：多項式の基底変更と、微分が単元である根での直積分解を合成する。
規約：第一射影は元の根を標準 étale 代数の指定根へ送る。
使われ方：局所の中心を因子として持つ中心を基底側で作る。
-/
theorem exists_standardEtale_tensor_adjoinRoot_split {R : Type*} [CommRing R]
    (P : StandardEtalePair R) :
    ∃ g : P.Ring[X], g.Monic ∧
      ∃ e : P.Ring ⊗[R] AdjoinRoot P.f ≃ₐ[P.Ring] P.Ring × AdjoinRoot g,
        (e (1 ⊗ₜ[R] AdjoinRoot.root P.f)).1 = P.X := by
  let B := P.Ring
  let f := P.f.map (algebraMap R B)
  have hf : f.Monic := P.monic_f.map _
  have hx : f.eval P.X = 0 := by
    simpa [f, eval_map, aeval_def] using P.hasMap_X.1
  have hd : IsUnit (f.derivative.eval P.X) := by
    simpa [f, derivative_map, eval_map, aeval_def] using P.hasMap_X.isUnit_derivative_f
  obtain ⟨g, hg, _, e, he⟩ := exists_adjoinRoot_split_of_isUnit_derivative_eval f hf P.X hx hd
  let q := P.f.map (Algebra.TensorProduct.includeRight (R := R) (A := B)).toRingHom
  let c := Algebra.TensorProduct.rid R B B
  have hq : q.map c.toRingHom = f := by
    rw [Polynomial.map_map]
    congr 1
    ext r
    change c ((1 : B) ⊗ₜ[R] r) = algebraMap R B r
    simp [c, Algebra.smul_def]
  let d := AdjoinRoot.mapAlgEquiv c q f (hq ▸ Associated.refl _)
  refine ⟨g, hg, (AdjoinRoot.tensorAlgEquiv (R := R) P.f q rfl).trans (d.trans e), ?_⟩
  change (e (d (AdjoinRoot.tensorAlgEquiv (R := R) P.f q rfl
    (1 ⊗ₜ[R] AdjoinRoot.root P.f)))).1 = P.X
  rw [AdjoinRoot.tensorAlgEquiv_root]
  have hroot : d (AdjoinRoot.root q) = AdjoinRoot.root f := by
    exact AdjoinRoot.map_root c.toRingHom q f hq.symm.dvd
  rwa [hroot]

end SerrePositivity.AlgebraicGeometry
