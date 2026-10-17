module

public import SerrePositivity.BhattScholze.Andre.MonicPrismaticFirstResidueKoszul
public import SerrePositivity.BhattScholze.DeltaDivisionFiniteSubfamilyTor

/-!
# André E1・E2：任意モニック族内の有限部分族の実残余 Tor

## 概要

任意モニック族内の有限部分族について、全ての有界 δ 深さの実評価関係は
Koszul 分解を与え、対応する実源グラフ商の高次 Tor は零となる。
BS Rem 7.15（著者版 p.62）の任意族への実余極限の入力。

## 方針

モニック族の最初の弱正則列を既存の部分族分離と δ 深さの帰納へ渡す。
源グラフの Koszul 分解と標準残余係数射により Tor を同定する。
原典の Prop 7.11 による証明とは異なる具体的 PD 計算の経路。

## 規約

添字型全体の有限性は要求しない。係数環の p 正則性と δ(d) の単元性を明示する。
正次数はここでは不要。

## 使われ方

有界深さ有限部分族図式の全段の Tor 消滅を供給する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (T : Set σ) (D : DeltaStructure p A) (d : A) (f : σ → Polynomial A)
variable {m : ℕ} (s : Fin m ≃ T)
local notation "P₁" => MvPolynomial σ A
local notation "L₁" => RelativeFreeDeltaRing (R := P₁) σ
local notation "E₁" => polynomialRankOneDeltaStructure σ D
local notation "c₁" => (fun t : σ => monicRelation (f t) t)
local notation "K₁" => Ideal.span {(p : L₁), MvPolynomial.C (MvPolynomial.C d)}
local notation "q₁" => Ideal.Quotient.mk K₁
local notation "α₁" => deltaDivisionSourceMap (σ := σ) E₁ (MvPolynomial.C d)
local notation "cs" N => deltaDivisionFiniteFamilyCoordinates (fun i => (s i : σ)) N

/-- 概要：任意モニック族の有限部分族の有界深さ実評価列は Koszul 分解を与える。
方針：モニック初項の弱正則性を一般部分族の δ 帰納へ渡す。
規約：全添字型の有限性と正次数は要求しない。
使われ方：BS Rem 7.15（著者版 p.62）の実余極限での Tor 消滅。 -/
theorem monicPrismaticFiniteSubfamilyEvaluation_isKoszulResolution (N : ℕ)
    (hf : ∀ t, (f t).Monic)
    (hpA : Function.Injective (fun z : A => (p : A) * z))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    SerrePositivity.IsKoszulResolution (fun i : Fin (cs N).length =>
      q₁ (deltaDivisionEvaluationRelation E₁ (MvPolynomial.C d) c₁
        ((cs N).get i).1 ((cs N).get i).2)) := by
  have hpP : IsSMulRegular P₁ (p : P₁) := by
    simpa only [map_natCast] using
      (show IsSMulRegular A (p : A) from hpA).of_flat (S := P₁)
  let vP := v.map (MvPolynomial.C : A →+* P₁).toMonoidHom
  have hvP : (vP : P₁) = (E₁).delta (MvPolynomial.C d) := by
    change MvPolynomial.C (v : A) = _
    rw [hv, polynomialRankOneDeltaStructure_delta_C]
  let η : σ × ℕ → L₁ ⧸ K₁ := fun z =>
    q₁ (deltaDivisionEvaluationRelation E₁ (MvPolynomial.C d) c₁ z.1 z.2)
  change SerrePositivity.IsKoszulResolution (η ∘ (cs N).get)
  apply SerrePositivity.isKoszulResolution_of_isWeaklyRegular
  rw [← List.map_ofFn, List.ofFn_get]
  exact deltaDivisionFiniteSubfamilyEvaluationList_isWeaklyRegular
    T E₁ (MvPolynomial.C d) c₁ s hpP vP hvP
    (monicPrismaticFirstRelation_mod_pd_fin_isWeaklyRegular D d f hf
      (fun i => (s i : σ)) (Subtype.coe_injective.comp s.injective)) N

/-- 概要：有限部分族の実源グラフ商の Tor は実残余評価 Koszul ホモロジーと同型。
方針：源グラフの分解と実残余係数射の関係式を使う。
規約：この比較にはモニック性も p 正則性も不要。
使われ方：BS Rem 7.15（著者版 p.62）の有界深さ入力。 -/
def monicPrismaticFiniteSubfamilySourceTorIso (N i : ℕ) :
    ((ModuleCat.extendScalars.{u, u, u} ((q₁).comp α₁)).leftDerived i).obj
      (ModuleCat.of L₁ (DeltaDivisionSourceFiniteCoordinateQuotient E₁ c₁ (cs N).get)) ≅
      (SerrePositivity.koszulComplex (fun j : Fin (cs N).length =>
        q₁ (deltaDivisionEvaluationRelation E₁ (MvPolynomial.C d) c₁
          ((cs N).get j).1 ((cs N).get j).2))).homology (-(i : ℤ)) := by
  have e := SerrePositivity.torAlgKoszulIso ((q₁).comp α₁)
    (fun j : Fin (cs N).length => deltaDivisionSourceGraphRelation E₁ c₁ ((cs N).get j))
    (deltaDivisionSourceGraph_fin_isKoszulResolution E₁ c₁ (cs N).get
      (deltaDivisionFiniteFamilyCoordinates_nodup _
        (Subtype.coe_injective.comp s.injective) N).injective_get) i
  have he : ((q₁).comp α₁) ∘
      (fun j : Fin (cs N).length => deltaDivisionSourceGraphRelation E₁ c₁ ((cs N).get j)) =
      (fun j : Fin (cs N).length => q₁ (deltaDivisionEvaluationRelation E₁ (MvPolynomial.C d) c₁
        ((cs N).get j).1 ((cs N).get j).2)) := by
    funext j
    exact congrArg q₁ (deltaDivisionSourceGraph_map E₁ (MvPolynomial.C d) c₁ ((cs N).get j))
  rw [he] at e
  exact e

/-- 概要：任意モニック族内の有限部分族の有界深さ源グラフ商の高次 Tor は零。
方針：実残余評価の Koszul 分解の非零次数消滅を Tor 比較で戻す。
規約：係数環の p 正則性と δ(d) の単元性だけを補助前提とする。
使われ方：BS Rem 7.15（著者版 p.62）の有限部分族図式。 -/
theorem monicPrismaticFiniteSubfamilySource_tor_subsingleton (N : ℕ)
    (hf : ∀ t, (f t).Monic)
    (hpA : Function.Injective (fun z : A => (p : A) * z))
    (v : Aˣ) (hv : (v : A) = D.delta d) (i : ℕ) :
    Subsingleton (SerrePositivity.TorAlg ((q₁).comp α₁) (i + 1)
      (DeltaDivisionSourceFiniteCoordinateQuotient E₁ c₁ (cs N).get)) := by
  have hr := monicPrismaticFiniteSubfamilyEvaluation_isKoszulResolution T D d f s N hf hpA v hv
  have hz := hr.isZero (-((i + 1 : ℕ) : ℤ)) (by omega)
  have ht := hz.of_iso (monicPrismaticFiniteSubfamilySourceTorIso T D d f s N (i + 1))
  exact ModuleCat.subsingleton_of_isZero ht

end SerrePositivity.BhattScholze.Andre
