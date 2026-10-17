module

public import SerrePositivity.BhattScholze.Andre.PowerRootPrismMonicRawRegular
public import SerrePositivity.BhattScholze.DeltaDivisionFiniteResidueKoszul
public import SerrePositivity.BhattScholze.DeltaDivisionMappedEvaluationKoszul
public import SerrePositivity.BhattScholze.DeltaDivisionSourceEvaluationColimitTor
public import SerrePositivity.HomologicalAlgebra.TorSequentialColimits

/-!
# hpR を使わない無限根モニック入力の実残余 Koszul 分解

## 概要
BS Rem 7.15（著者版 p.62）の元の raw 包について、mod(p,d) の有限 δ 関係列は
hpR なしに Koszul 分解を与える。

## 方針
初項は負のモニック入力であり、係数二元商上で正則。
以後は既存の distinguished 係数と Witt 計算による残余正則列を使う。

## 規約
mod p の d の正則性や raw 環の p 正則性を仮定しない。

## 使われ方
正則対の経路を使わず、元の完備化の実導来剰余を計算するための入力。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
variable (f : Polynomial A) (hf : f.Monic)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => PowerRootPolynomial A p hp
local notation "E" => powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
local notation "dP" => algebraMap A P W.generator
local notation "a" => powerRootPrismMonicUnaryFamily (p := p) f
local notation "L₀" => PowerRootUnaryFreeDeltaRing A p hp
local notation "KP" => Ideal.span {(p : P), dP}
local notation "K" => Ideal.span {(p : L₀), MvPolynomial.C dP}
local notation "q" => Ideal.Quotient.mk K

include hf in
/-- 概要：最初の実 δ 関係は mod(p,d) の自由環で正則。
方針：係数商との交換で負のモニック入力へ移し、多項式の平坦性を用いる。
規約：d mod p の正則性は不要。
使われ方：BS Rem 7.15（著者版 p.62）の hpR なしの有限残余帰納法の初項。 -/
theorem powerRootPrismMonicFirst_mod_pair_regular_of_unconditional :
    IsSMulRegular (L₀ ⧸ K) (q (deltaDivisionIteratedRelation E dP a default 0)) := by
  have hK : (KP).map (MvPolynomial.C : P →+* L₀) = K := by
    rw [Ideal.map_span, Set.image_pair, map_natCast]
  let e := (Ideal.quotEquivOfEq hK.symm).trans
    (MvPolynomial.quotientEquivQuotientMvPolynomial
      (σ := PUnit.{u + 1} × ℕ) KP).symm.toRingEquiv
  have he (x : L₀) : e (q x) = MvPolynomial.map (Ideal.Quotient.mk KP) x := by
    rw [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
    exact RingHom.congr_fun (monicPowerFamilyCoefficientQuotient_comp
      (PUnit.{u + 1} × ℕ) P KP) x
  have hd : Ideal.Quotient.mk KP dP = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  apply (ringEquiv_isSMulRegular e _).mpr
  rw [he]
  change IsSMulRegular _ (MvPolynomial.map (Ideal.Quotient.mk KP)
    (MvPolynomial.C dP * MvPolynomial.X (default, 0) -
      MvPolynomial.C (powerRootMonicPDInput p f)))
  rw [map_sub, map_mul, MvPolynomial.map_C, MvPolynomial.map_X,
    MvPolynomial.map_C, hd, map_zero, zero_mul, zero_sub]
  have hr := powerRootPolynomial_monic_mod_pair_regular p hp W.generator f hf
  have hl := hr.of_flat (S := MvPolynomial (PUnit.{u + 1} × ℕ) (P ⧸ KP))
  intro x y hxy
  apply hl
  simpa only [smul_eq_mul, neg_mul, neg_inj, MvPolynomial.algebraMap_eq,
    powerRootMonicPDInput] using hxy

include hf in
/-- 概要：元の有限 δ 関係列は mod(p,d) で全深さにおいて弱正則。
方針：モニック初項、完全 prism の p 正則性、自由環の ghost 単射性を一般残余定理へ渡す。
規約：hpR や正次数を追加せず、元の全有限関係を使う。
使われ方：BS Rem 7.15（著者版 p.62）の無条件の実導来還元の Tor 消滅。 -/
theorem powerRootPrismMonicFiniteResidue_isWeaklyRegular_of_unconditional (N : ℕ) :
    RingTheory.Sequence.IsWeaklyRegular (L₀ ⧸ K)
      (List.ofFn fun i : Fin (N + 1) =>
        q (deltaDivisionIteratedRelation E dP a default i.val)) := by
  have hpP := powerRootPolynomial_primeRegular p hW.p_mul_injective
  have hpL : Function.Injective (fun x : L₀ => (p : L₀) * x) := by
    simpa only [map_natCast, IsSMulRegular, smul_eq_mul] using
      (show IsSMulRegular P (p : P) from hpP).of_flat (S := L₀)
  let hd := powerRootPrismGenerator_isDistinguished W hW
  exact deltaDivisionFiniteResidueRelations_isWeaklyRegular E dP a hpP hpL
    (witt_ghostMap_injective_of_mul_prime_injective p L₀ hpL) hd.unit hd.unit_spec
    (powerRootPrismMonicFirst_mod_pair_regular_of_unconditional W hW f hf) N

include hf in
/-- 概要：元の有限 δ 関係列は mod(p,d) で Koszul 分解。
方針：既証の弱正則列の分解判定を適用する。
規約：hpR と正次数は不要。
使われ方：BS Rem 7.15（著者版 p.62）の実剰余 Tor 計算。 -/
theorem powerRootPrismMonicFiniteResidue_isKoszulResolution_of_unconditional (N : ℕ) :
    SerrePositivity.IsKoszulResolution (fun i : Fin (N + 1) =>
      q (deltaDivisionIteratedRelation E dP a default i.val)) :=
  SerrePositivity.isKoszulResolution_of_isWeaklyRegular _
    (powerRootPrismMonicFiniteResidue_isWeaklyRegular_of_unconditional W hW f hf N)

include hf in
/-- 概要：実評価関係の全有限深さの残余 Koszul 複体も分解を与える。
方針：δ 反復列と実評価列の三角比較を用いる。
規約：元の係数商・実関係を保つ。
使われ方：BS Rem 7.15（著者版 p.62）の全評価源への Tor 移送。 -/
theorem powerRootPrismMonicFiniteResidueEvaluation_isKoszulResolution_of_unconditional
    (N : ℕ) :
    SerrePositivity.IsKoszulResolution (fun i : Fin (N + 1) =>
      q (deltaDivisionEvaluationRelation E dP a default i.val)) :=
  deltaDivisionMappedEvaluation_isKoszulResolution E dP a q
    (fun N => powerRootPrismMonicFiniteResidue_isWeaklyRegular_of_unconditional W hW f hf N) N

local notation "ψ" => RingHom.comp q (deltaDivisionSourceMap E dP)

include hf in
/-- 概要：実残余自由 δ 射に沿う一つの有限源商の正次数 Tor は零。
方針：源グラフの Koszul 分解で実評価関係のホモロジーへ移す。
規約：δ 深さと正次数のすべてを扱う。
使われ方：BS Rem 7.15（著者版 p.62）の無条件の実導来剰余比較の有限入力。 -/
theorem powerRootPrismMonicFiniteResidueSource_tor_subsingleton_of_unconditional
    (N i : ℕ) :
    Subsingleton (SerrePositivity.TorAlg ψ (i + 1)
      (DeltaDivisionEvaluationSourceFiniteQuotient E a N)) := by
  let cs : Fin (N + 1) → PUnit.{u + 1} × ℕ := fun j => (default, j.val)
  have hcs : Function.Injective cs := by
    intro x y hxy
    exact Fin.ext (congrArg Prod.snd hxy)
  have e := SerrePositivity.torAlgKoszulIso ψ
    (fun j => deltaDivisionSourceGraphRelation E a (cs j))
    (deltaDivisionSourceGraph_fin_isKoszulResolution E a cs hcs) (i + 1)
  have he : ψ ∘ (fun j => deltaDivisionSourceGraphRelation E a (cs j)) =
      (fun j : Fin (N + 1) => q (deltaDivisionEvaluationRelation E dP a default j.val)) := by
    funext j
    exact congrArg q (deltaDivisionSourceGraph_map E dP a (cs j))
  rw [he] at e
  have hr := powerRootPrismMonicFiniteResidueEvaluation_isKoszulResolution_of_unconditional
    W hW f hf N
  exact ModuleCat.subsingleton_of_isZero
    ((hr.isZero (-((i + 1 : ℕ) : ℤ)) (by omega)).of_iso e)

include hf in
/-- 概要：元の全評価源の、実残余自由 δ 射に沿う正次数 Tor は零。
方針：有限深さの消滅を、証明済みの Tor と逐次余極限の交換で全評価環へ渡す。
規約：hpR や新しい交換仮定を残さない。
使われ方：BS Rem 7.15（著者版 p.62）の無条件の標準導来 augmentation の入力。 -/
theorem powerRootPrismMonicResidueSource_tor_subsingleton_of_unconditional (i : ℕ) :
    letI := deltaDivisionSourceEvaluationAlgebra E a
    Subsingleton (SerrePositivity.TorAlg ψ (i + 1) P) := by
  let := deltaDivisionSourceEvaluationAlgebra E a
  let := SerrePositivity.torAlg_preservesSequentialColimits ψ (i + 1)
  exact deltaDivisionEvaluationSource_tor_subsingleton_of_preservesColimit E a ψ i
    (fun N => powerRootPrismMonicFiniteResidueSource_tor_subsingleton_of_unconditional
      W hW f hf N i) inferInstance

end SerrePositivity.BhattScholze.Andre
