module
public import SerrePositivity.Util.Citation

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateCompletedMap
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineGeneratorClasses
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.FinitePolynomialCartier
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.CartierCompletedForms
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.CartierCompletedForms
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateCompletedMap
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateAffineForms
import all SerrePositivity.CommutativeAlgebra.DeRham.UniversalProperty

/-!
# Hodge–Tate と inverse Cartier の照合

## 概要
結晶比較を通した Hodge–Tate 写像は、零次と一次の生成元での値で決まる。

## 方針
係数の素体を加法的に比較し、外積の生成元で一致を全次数へ延ばす。

## 規約
標数 p の完備形式は完備化の単位を逆にして通常の形式と同一視する。

## 使われ方
結晶基底の多項式 Hodge–Tate 同型。
-/

public noncomputable section

open CategoryTheory SerrePositivity.Cosimplicial SerrePositivity.DeRham
open scoped Simplicial TensorProduct

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable (p : ℕ) [Fact p.Prime] (r : ℕ)

local notation "Z" => crystallineBasePrism p
local notation "hZ" => crystallineBaseBounded p
local notation "k" => cartierBase p
local notation "T" => formVars r
local notation "Φ" => finitePolynomialCartier p r
local notation "η" => hodgeTateMap Z hZ r
local notation "Ψ" => crystallineChain p r

private def cartierComparison (i : ℕ) : forms (cartierBase.{u} p) (formVars.{u} r) i →+
    (deRhamComplex (cartierBase.{u} p) (formVars.{u} r)).homology i :=
  (Ψ i).toAddMonoidHom.comp (((η).app i).toAddMonoidHom.comp (completedFormsUnit k T p i))

set_option backward.isDefEq.respectTransparency false in
private theorem cartierComparison_wedge {i j : ℕ}
    (x : forms (cartierBase.{u} p) (formVars.{u} r) i) (y : forms (cartierBase.{u} p) (formVars.{u} r) j) :
    cartierComparison p r (i+j) (wedge k T x y) =
      deRhamCohomologyWedge k T (cartierComparison p r i x) (cartierComparison p r j y) := by
  change Ψ (i+j) ((η).app (i+j) (completedFormsUnit k T p (i+j) (wedge k T x y))) = _
  rw [← completedWedge_unit]
  exact (congrArg (Ψ (i+j)) ((η).product (completedFormsUnit k T p i x)
    (completedFormsUnit k T p j y))).trans (crystallineChain_cup p r _ _)

set_option backward.isDefEq.respectTransparency false in
private theorem cartierComparison_one :
    cartierComparison.{u} p r 0 (formsZeroEquiv (cartierBase.{u} p) (formVars.{u} r) 1) =
      (Φ).app 0 (formsZeroEquiv k T 1) := by
  let e := formsZeroEquiv (cartierBase.{u} p) (formVars.{u} r)
  let c := (Φ).app 0 (e 1)
  let a := Ψ 0 (1 : hodgeTateCohomology' Z hZ r 0)
  have ha : cartierComparison p r 0 (e 1) = a := by
    change Ψ 0 ((η).app 0 (completedFormsUnit k T p 0 (e 1))) = a
    rw [← degreeZeroForm_unit_raw, (η).on_zero, map_one, map_one]
  rw [ha]
  change a = c
  obtain ⟨x, hx⟩ := ((Φ).app 0).surjective a
  have hleft : deRhamCohomologyWedge k T c a = a := by
    rw [← hx, ← (Φ).mul]
    congr 1
    have h := formsZero_wedge Z r 0 (1 : Poly k T) x
    simpa only [Nat.zero_add, cast_eq, one_smul] using h
  obtain ⟨z, hz⟩ := (Ψ 0).surjective c
  have hright : deRhamCohomologyWedge k T c a = c := by
    rw [← hz]
    change deRhamCohomologyWedge k T (Ψ 0 z) (Ψ 0 1) = Ψ 0 z
    rw [← crystallineChain_cup, cohomologyCup_one_right]
  exact hleft.symm.trans hright

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 120000 in
set_option backward.isDefEq.respectTransparency false in
private theorem cartierComparison_zero
    (hX : ∀ t : formVars.{u} r, cartierComparison.{u} p r 0 (formsZeroEquiv k T (MvPolynomial.X t)) =
      (Φ).app 0 (formsZeroEquiv k T (MvPolynomial.X t)))
    (f : Poly (cartierBase.{u} p) (formVars.{u} r)) :
    cartierComparison p r 0 (formsZeroEquiv k T f) = (Φ).app 0 (formsZeroEquiv k T f) := by
  let e := formsZeroEquiv (cartierBase.{u} p) (formVars.{u} r)
  let F := cartierComparison.{u} p r 0
  let G := (Φ).app 0
  change F (e f) = G (e f)
  induction f using MvPolynomial.induction_on with
  | C c =>
    let : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    obtain ⟨n, hn⟩ := ZMod.natCast_zmod_surjective ((cartierBaseEquiv p) c)
    have hc : (n : k) = c := (cartierBaseEquiv p).injective ((map_natCast _ n).trans hn)
    rw [← hc, map_natCast, ← nsmul_one, map_nsmul, map_nsmul, map_nsmul,
      cartierComparison_one p r]
  | add f g hf hg => rw [map_add, map_add, map_add, hf, hg]
  | mul_X f t hf =>
    have hw : wedge k T (e f) (e (MvPolynomial.X t)) = e (f * MvPolynomial.X t) := by
      have h := formsZero_wedge Z r 0 f (e (MvPolynomial.X t))
      rw [show f • e (MvPolynomial.X t) = e (f * MvPolynomial.X t) by
        exact ((polynomialZeroForm Z r).map_smul f (MvPolynomial.X t)).symm] at h
      exact h
    rw [← hw]
    exact (cartierComparison_wedge p r (e f) (e (MvPolynomial.X t))).trans
      ((congrArg₂ (deRhamCohomologyWedge k T) hf (hX t)).trans
        ((Φ).mul (e f) (e (MvPolynomial.X t))).symm)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 120000 in
set_option backward.isDefEq.respectTransparency false in
private theorem cartierComparison_all
    (hX : ∀ t : formVars.{u} r, cartierComparison.{u} p r 0 (formsZeroEquiv k T (MvPolynomial.X t)) =
      (Φ).app 0 (formsZeroEquiv k T (MvPolynomial.X t)))
    (hdX : ∀ t : formVars.{u} r, cartierComparison.{u} p r 1 (dX k T t) = (Φ).app 1 (dX k T t))
    (i : ℕ) (x : forms (cartierBase.{u} p) (formVars.{u} r) i) :
    cartierComparison p r i x = (Φ).app i x := by
  let F := cartierComparison.{u} p r
  let G := (Φ).app
  have h₀ (f : Poly k T) : F 0 (formsZeroEquiv k T f) = G 0 (formsZeroEquiv k T f) :=
    cartierComparison_zero p r hX f
  have hmul {i j : ℕ} (x : forms k T i) (y : forms k T j)
      (hx : F i x = G i x) (hy : F j y = G j y) :
      F (i+j) (wedge k T x y) = G (i+j) (wedge k T x y) := by
    change cartierComparison p r (i+j) (wedge k T x y) = (Φ).app (i+j) (wedge k T x y)
    exact (cartierComparison_wedge p r x y).trans
      ((congrArg₂ (deRhamCohomologyWedge k T) hx hy).trans ((Φ).mul x y).symm)
  apply forms_induction (P := fun i x => F i x = G i x)
  · intro i
    rw [map_zero, map_zero]
  · intro i x y hx hy
    rw [map_add, map_add, hx, hy]
  · exact h₀
  · intro v
    have hv : v = ∑ t : T, v t • Pi.single t 1 := by
      simpa only [Pi.basisFun_repr, Pi.basisFun_apply] using ((Pi.basisFun k T).sum_repr v).symm
    rw [hv, map_sum, map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro t _
    rw [constantOneForm_smul]
    have h := hmul (formsZeroEquiv k T (MvPolynomial.C (v t))) (dX k T t) (h₀ _) (hdX t)
    have hw := formsZero_wedge Z r 1 (MvPolynomial.C (v t)) (dX k T t)
    change F 1 (wedge k T (formsZeroEquiv k T (MvPolynomial.C (v t))) (dX k T t)) =
      G 1 (wedge k T (formsZeroEquiv k T (MvPolynomial.C (v t))) (dX k T t)) at h
    have hw' : wedge k T (formsZeroEquiv k T (MvPolynomial.C (v t))) (dX k T t) =
        (MvPolynomial.C (v t) : Poly k T) • dX k T t := by
      simpa only [Nat.zero_add, cast_eq] using hw
    rw [hw'] at h
    exact h
  · exact hmul

set_option maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
private theorem cartierComparison_matches
    (hX : ∀ t : formVars.{u} r, cartierComparison.{u} p r 0 (formsZeroEquiv k T (MvPolynomial.X t)) =
      (Φ).app 0 (formsZeroEquiv k T (MvPolynomial.X t)))
    (hdX : ∀ t : formVars.{u} r, cartierComparison.{u} p r 1 (dX k T t) = (Φ).app 1 (dX k T t))
    (i : ℕ) (x : affineForms (crystallineBasePrism.{u} p) r i) :
    Ψ i ((η).app i x) = (Φ).app i (cartierFormsIso p r i x) := by
  let e := cartierFormsIso.{u} p r i
  have hu : completedFormsUnit k T p i (e x) = x := by
    apply e.injective
    exact cartierCompletedFormsIso_unit p (formVars.{u} r) i (e x)
  have h := cartierComparison_all p r hX hdX i (e x)
  change Ψ i ((η).app i (completedFormsUnit k T p i (e x))) = (Φ).app i (e x) at h
  rwa [hu] at h

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 120000 in
set_option backward.isDefEq.respectTransparency false in
/-- 結晶基底の多項式 Hodge–Tate 写像は de Rham 比較と inverse Cartier により全単射。 -/
theorem hodgeTate_of_deRham_cartier :
    HodgeTateIsoStatement (crystallineBasePrism.{u} p) (crystallineBaseBounded p) r := by
  have hX (t : formVars.{u} r) :
      cartierComparison.{u} p r 0 (formsZeroEquiv k T (MvPolynomial.X t)) =
        (Φ).app 0 (formsZeroEquiv k T (MvPolynomial.X t)) := by
    change Ψ 0 ((η).app 0 (completedFormsUnit k T p 0 (formsZeroEquiv k T (MvPolynomial.X t)))) = _
    rw [← degreeZeroForm_unit_raw, (η).on_zero]
    have hc : rawCoefficient (crystallineBasePrism.{u} p) r (MvPolynomial.X t) =
        prismPolynomialUnit (crystallineBasePrism.{u} p) (Fin r) (MvPolynomial.X t.down) := by
      apply (affineCoordinateIso (crystallineBasePrism.{u} p) r).injective
      let e := affineCoordinateIso (crystallineBasePrism.{u} p) r
      change e (e.symm (algebraMap (Poly k T) (completedPoly k T p) (MvPolynomial.X t))) = _
      rw [RingEquiv.apply_symm_apply, affineCoordinateIso_X]
    rw [hc]
    exact (crystallineChain_generators.{u} p r t.down).1
  have hdX (t : formVars.{u} r) :
      cartierComparison.{u} p r 1 (dX k T t) = (Φ).app 1 (dX k T t) := by
    change Ψ 1 ((η).app 1 (completedFormsUnit k T p 1 (dX k T t))) = _
    rw [(η).on_one]
    exact (crystallineChain_generators.{u} p r t.down).2
  intro i
  let G := (cartierFormsIso.{u} p r i).trans (((Φ).app i).trans (Ψ i).symm)
  have h : ⇑((η).app i) = ⇑G := by
    funext x
    apply (Ψ i).injective
    change Ψ i ((η).app i x) = Ψ i ((Ψ i).symm ((Φ).app i (cartierFormsIso p r i x)))
    rw [AddEquiv.apply_symm_apply]
    exact cartierComparison_matches p r hX hdX i x
  rw [h]
  exact G.bijective

end SerrePositivity.BhattScholze.Prismatic

/-! Reviewed literature correspondences. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Cor 5.5" (partial := special) "結晶基底 (Z_p,(p)) の多項式の場合を de Rham 比較と inverse Cartier で直接証明（D68 改訂、BS-D68 停止点 3）。一般の結晶 prism 上の S = A/p[X]（Lemma 4.20 で帰着）は drafts ／ 11-10 更新（2）"] _root_.SerrePositivity.BhattScholze.Prismatic.hodgeTate_of_deRham_cartier
attribute [cite BS19 "Thm 4.11" (partial := component) "主張の型（HodgeTateIsoStatement）と結晶基底 (Z_p,(p)) の場合は本体（BS-D68）。一般の有界向き付き基底への帰着（Prop 6.2・Thm 6.3）は drafts ／ 11-10 更新（2）。本体の HodgeTateIsoStatement は Rem 4.19 の鎖複体の模型（reducedModel）のコホモロジーについての主張で、site の RΓ ではない ／ 11-12 夜更新（§4 の見直し）"] _root_.SerrePositivity.BhattScholze.Prismatic.hodgeTate_of_deRham_cartier
