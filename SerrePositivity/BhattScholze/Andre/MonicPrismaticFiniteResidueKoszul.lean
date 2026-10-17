module

public import SerrePositivity.BhattScholze.Andre.MonicPrismaticFirstResidueKoszul
public import SerrePositivity.BhattScholze.DeltaDivisionFiniteFamilyEvaluation

/-!
# André E1・E2：有限モニック族の全有限 δ 深さの残余 Koszul 分解

## 概要

一般 f/d 包の実 (p,d) 商上で、有限モニック族の全有限 δ 深さの関係が Koszul 分解を与える。
BS Rem 7.15（著者版 p.62）の実導来剰余の離散性への入力。

## 方針

最初の関係の弱正則性を一般 δ 除算の既存帰納へ渡し、評価関係へ移す。
原典の Prop 7.11 を使う経路とは異なる明示関係の計算。

## 規約

p 正則な係数環と δ(d) の単元性を仮定する。正次数は不要。

## 使われ方

実残余自由 δ 射に沿う全評価源の高次 Tor 消滅へ渡す。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (f : σ → Polynomial A)
local notation "P₁" => MvPolynomial σ A
local notation "L₁" => RelativeFreeDeltaRing (R := P₁) σ
local notation "E₁" => polynomialRankOneDeltaStructure σ D
local notation "bRel" => (fun s : σ => monicRelation (f s) s)
local notation "K₁" => Ideal.span {(p : L₁), MvPolynomial.C (MvPolynomial.C d)}

/-- 概要：任意モニック関係族については、係数のp正則性とδd単元だけで全有限δ深さが弱正則。
方針：最初のモニック弱正則列を、一般 δ 除算の既存有限深さ定理に渡す。
規約：係数環の p 正則性と δ(d) の単元性を要求する。正次数は不要。
使われ方：BS Rem 7.15（著者版 p.62）の実導来剰余の Tor 消滅入力。 -/
theorem monicPrismaticFiniteResidueFamilyList_isWeaklyRegular
    (hf : ∀ s, (f s).Monic) {m : ℕ} (s : Fin m ≃ σ)
    (hpA : Function.Injective (fun z : A => (p : A) * z))
    (v : Aˣ) (hv : (v : A) = D.delta d) (N : ℕ) :
    RingTheory.Sequence.IsWeaklyRegular (L₁ ⧸ K₁)
      (deltaDivisionFiniteResidueFamilyList E₁ (MvPolynomial.C d) bRel s N) := by
  have hpP : IsSMulRegular P₁ (p : P₁) := by
    simpa only [map_natCast] using
      (show IsSMulRegular A (p : A) from hpA).of_flat (S := P₁)
  have hpL : IsSMulRegular L₁ (p : L₁) := by
    simpa only [map_natCast] using hpP.of_flat (S := L₁)
  let vP := v.map (MvPolynomial.C : A →+* P₁).toMonoidHom
  have hvP : (vP : P₁) = (E₁).delta (MvPolynomial.C d) := by
    change MvPolynomial.C (v : A) = _
    rw [hv, polynomialRankOneDeltaStructure_delta_C]
  exact deltaDivisionFiniteResidueFamilyList_isWeaklyRegular E₁ (MvPolynomial.C d) bRel s
    hpP hpL (witt_ghostMap_injective_of_mul_prime_injective p L₁ hpL) vP hvP
    (monicPrismaticFirstRelation_mod_pd_fin_isWeaklyRegular D d f hf s s.injective) N

/-- 概要：有限モニック族の全有限δ深さの実mod(p,d)Koszul分解。
方針：最初のモニック弱正則列を、一般 δ 除算の既存有限深さ定理に渡す。
規約：係数環の p 正則性と δ(d) の単元性を要求する。正次数は不要。
使われ方：BS Rem 7.15（著者版 p.62）の実導来剰余の Tor 消滅入力。 -/
theorem monicPrismaticFiniteResidueFamilyList_isKoszulResolution
    (hf : ∀ s, (f s).Monic) {m : ℕ} (s : Fin m ≃ σ)
    (hpA : Function.Injective (fun z : A => (p : A) * z))
    (v : Aˣ) (hv : (v : A) = D.delta d) (N : ℕ) :
    SerrePositivity.IsKoszulResolution
      (deltaDivisionFiniteResidueFamilyList E₁ (MvPolynomial.C d) bRel s N).get := by
  apply SerrePositivity.isKoszulResolution_of_isWeaklyRegular
  simpa only [List.ofFn_get] using
    monicPrismaticFiniteResidueFamilyList_isWeaklyRegular D d f hf s hpA v hv N


variable {m : ℕ} (s : Fin m ≃ σ) (N : ℕ)
local notation "cs" => deltaDivisionFiniteFamilyCoordinates (s : Fin m → σ) N
local notation "q₁" => Ideal.Quotient.mk K₁
local notation "α₁" => deltaDivisionSourceMap (σ := σ) E₁ (MvPolynomial.C d)

/-- 概要：全有限 δ 座標の実残余評価関係は Koszul 分解を与える。
方針：残余関係リストの弱正則性を既存の評価リストの弱正則性へ渡す。
規約：有限添字型の全列挙を明示する。正次数は不要。
使われ方：BS Rem 7.15（著者版 p.62）の残余自由 δ 射に沿う源商の Tor 消滅。 -/
theorem monicPrismaticFiniteResidueEvaluationFamily_isKoszulResolution
    (hf : ∀ s, (f s).Monic)
    (hpA : Function.Injective (fun z : A => (p : A) * z))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    SerrePositivity.IsKoszulResolution (fun i : Fin (cs).length =>
      q₁ (deltaDivisionEvaluationRelation E₁ (MvPolynomial.C d) bRel
        ((cs).get i).1 ((cs).get i).2)) := by
  let g : σ × ℕ → L₁ ⧸ K₁ := fun z =>
    q₁ (deltaDivisionEvaluationRelation E₁ (MvPolynomial.C d) bRel z.1 z.2)
  change SerrePositivity.IsKoszulResolution (g ∘ (cs).get)
  apply SerrePositivity.isKoszulResolution_of_isWeaklyRegular
  rw [← List.map_ofFn, List.ofFn_get]
  exact deltaDivisionFiniteEvaluationFamilyList_isWeaklyRegular E₁ (MvPolynomial.C d) bRel s
    (fun k => monicPrismaticFiniteResidueFamilyList_isWeaklyRegular D d f hf s hpA v hv k) N

/-- 概要：有限モニック族の全有限 δ 深さの源グラフ商は、残余自由 δ 射に沿う高次 Tor が零。
方針：源グラフの Koszul 分解を実残余評価 Koszul ホモロジーへ移し、消滅を適用する。
規約：実射は一般除算源射と実 (p,d) 商射の合成で固定する。
使われ方：BS Rem 7.15（著者版 p.62）の全深さ評価源の離散性への有限段入力。 -/
theorem monicPrismaticFiniteResidueEvaluationFamilySource_tor_subsingleton
    (hf : ∀ s, (f s).Monic)
    (hpA : Function.Injective (fun z : A => (p : A) * z))
    (v : Aˣ) (hv : (v : A) = D.delta d) (i : ℕ) :
    Subsingleton (SerrePositivity.TorAlg ((q₁).comp α₁) (i + 1)
      (DeltaDivisionSourceFiniteCoordinateQuotient E₁ bRel (cs).get)) := by
  have e := SerrePositivity.torAlgKoszulIso ((q₁).comp α₁)
    (fun j : Fin (cs).length => deltaDivisionSourceGraphRelation E₁ bRel ((cs).get j))
    (deltaDivisionSourceGraph_fin_isKoszulResolution E₁ bRel (cs).get
      (deltaDivisionFiniteFamilyCoordinates_nodup s s.injective N).injective_get) (i + 1)
  have he : ((q₁).comp α₁) ∘
      (fun j : Fin (cs).length => deltaDivisionSourceGraphRelation E₁ bRel ((cs).get j)) =
      (fun j : Fin (cs).length => q₁ (deltaDivisionEvaluationRelation E₁ (MvPolynomial.C d) bRel
        ((cs).get j).1 ((cs).get j).2)) := by
    funext j
    exact congrArg q₁ (deltaDivisionSourceGraph_map E₁ (MvPolynomial.C d) bRel ((cs).get j))
  rw [he] at e
  have hr := monicPrismaticFiniteResidueEvaluationFamily_isKoszulResolution D d f s N hf hpA v hv
  exact ModuleCat.subsingleton_of_isZero ((hr.isZero (-((i + 1 : ℕ) : ℤ)) (by omega)).of_iso e)

end SerrePositivity.BhattScholze.Andre
