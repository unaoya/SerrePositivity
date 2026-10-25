module

public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.Division.DeltaDivisionBoundedSupportColimit
public import SerrePositivity.BhattScholze.Andre.Variants.MonicPrismaticFiniteSubfamilyTor
public import SerrePositivity.HomologicalAlgebra.TorExactColimits
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import SerrePositivity.HomologicalAlgebra.TorSymmetry
public import SerrePositivity.HomologicalAlgebra.DerivedTensorBaseChange
public import SerrePositivity.HomologicalAlgebra.DerivedBaseChangeDiscrete

/-!
# André E1・E2：任意モニック族の実残余評価の Tor 消滅

## 概要

任意モニック族の有界深さ有限部分族図式の全段、および全評価源の高次 Tor は零。
BS Rem 7.15（著者版 p.62）の任意族の実導来剰余計算。

## 方針

既存の有限部分族の Koszul 分解と実評価図式の余極限を使い、
同じ TorAlg 関手が有限部分集合図式の余極限を保つことを適用する。
原典の Prop 7.11 による証明とは異なる PD 計算の経路。

## 規約

添字型全体は任意。p 正則性と δ(d) の単元性を明示し、正次数を要求しない。
余極限の保存は既存の一般定理から供給し、外部仮定には残さない。

## 使われ方

実残余係数射に沿う全評価源の Tor 非輪状性を供給する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {σ : Type u}

private theorem coordinate_range {m : ℕ} (T : Finset σ) (s : Fin m ≃ T) (N : ℕ) :
    Set.range (deltaDivisionFiniteFamilyCoordinates (fun i => (s i : σ)) N).get =
      {z : σ × ℕ | z.1 ∈ T ∧ z.2 ≤ N} := by
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    obtain ⟨j, k, hk, he⟩ :=
      (deltaDivisionFiniteFamilyCoordinates_mem (fun i => (s i : σ)) N _).mp (List.get_mem _ i)
    rw [← he]
    exact ⟨(s j).property, hk⟩
  · rintro ⟨hz, hn⟩
    obtain ⟨j, hj⟩ := s.surjective ⟨z.1, hz⟩
    have hm : z ∈ deltaDivisionFiniteFamilyCoordinates (fun i => (s i : σ)) N :=
      (deltaDivisionFiniteFamilyCoordinates_mem (fun i => (s i : σ)) N z).mpr
        ⟨j, z.2, hn, Prod.ext (congrArg Subtype.val hj) rfl⟩
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hm
    exact ⟨i, hi⟩

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (f : σ → Polynomial A)
local notation "P" => MvPolynomial σ A
local notation "L" => RelativeFreeDeltaRing (R := P) σ
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => (fun t : σ => monicRelation (f t) t)
local notation "I" => Ideal.span {(p : L), MvPolynomial.C (MvPolynomial.C d)}
local notation "ψ" => RingHom.comp (Ideal.Quotient.mk I)
  (deltaDivisionSourceMap (σ := σ) E (MvPolynomial.C d))
local notation "F" => deltaDivisionBoundedSupportModuleDiagram E r
local notation "K" => deltaDivisionEvaluationFiniteSupportIdeal E r

/-- 概要：任意モニック族の有界深さ評価図式の全段の高次 Tor は零。
方針：有限座標の hull を選び、有限部分族の源グラフ商へ同定する。
規約：全添字型の有限性は不要。
使われ方：BS Rem 7.15（著者版 p.62）の実余極限の段ごとの入力。 -/
theorem monicPrismaticBoundedSupportStage_tor_subsingleton
    (hf : ∀ t, (f t).Monic)
    (hpA : Function.Injective (fun z : A => (p : A) * z))
    (v : Aˣ) (hv : (v : A) = D.delta d) (S : Finset (σ × ℕ)) (i : ℕ) :
    Subsingleton (((ModuleCat.extendScalars.{u, u, u} ψ).leftDerived (i + 1)).obj ((F).obj S)) := by
  classical
  let T := S.image Prod.fst
  let N := S.sup Prod.snd
  let s : Fin T.card ≃ T := (Finset.equivFin T).symm
  let cs := deltaDivisionFiniteFamilyCoordinates (fun j => (s j : σ)) N
  have hcoords : Set.range cs.get = (deltaDivisionCoordinateHull S : Set (σ × ℕ)) := by
    rw [coordinate_range T s N]
    ext z
    exact (mem_deltaDivisionCoordinateHull S z).symm
  have hK : K (deltaDivisionCoordinateHull S) =
      Ideal.span (Set.range fun j => deltaDivisionSourceGraphRelation E r (cs.get j)) := by
    change Ideal.span (deltaDivisionSourceGraphRelation E r ''
      (deltaDivisionCoordinateHull S : Set (σ × ℕ))) = _
    rw [← hcoords, ← Set.range_comp']
  let e : (F).obj S ≅
      ModuleCat.of L (DeltaDivisionSourceFiniteCoordinateQuotient E r cs.get) :=
    (Submodule.quotEquivOfEq _ _ (show (K (deltaDivisionCoordinateHull S) : Submodule L L) =
      Ideal.span (Set.range fun j => deltaDivisionSourceGraphRelation E r (cs.get j))
        from hK)).toModuleIso
  let H := (ModuleCat.extendScalars.{u, u, u} ψ).leftDerived (i + 1)
  have ht := monicPrismaticFiniteSubfamilySource_tor_subsingleton
    (T : Set σ) D d f s N hf hpA v hv i
  have hz : IsZero (H.obj
      (ModuleCat.of L (DeltaDivisionSourceFiniteCoordinateQuotient E r cs.get))) := by
    let := ht
    exact ModuleCat.isZero_of_subsingleton _
  exact ModuleCat.subsingleton_of_isZero (hz.of_iso (H.mapIso e))

/-- 概要：実図式の Tor 交換から、任意モニック族の全評価環の高次 Tor が消える。
方針：各段の消滅を余極限に移し、元の評価環との標準同型を使う。
規約：この中間補題の保存仮定は後の公開入口で解消する。
使われ方：BS Rem 7.15（著者版 p.62）の全評価源。 -/
theorem monicPrismaticEvaluation_tor_subsingleton_of_preservesBoundedSupportColimit
    (hf : ∀ t, (f t).Monic)
    (hpA : Function.Injective (fun z : A => (p : A) * z))
    (v : Aˣ) (hv : (v : A) = D.delta d) (i : ℕ)
    (hpres : PreservesColimit F ((ModuleCat.extendScalars.{u, u, u} ψ).leftDerived (i + 1))) :
    letI := deltaDivisionSourceEvaluationAlgebra E r
    Subsingleton (SerrePositivity.TorAlg ψ (i + 1) P) := by
  let := deltaDivisionSourceEvaluationAlgebra E r
  let := hpres
  let H := (ModuleCat.extendScalars.{u, u, u} ψ).leftDerived (i + 1)
  have hz : IsZero (H.obj (colimit F)) :=
    torAlg_finsetColimit_isZero_of_stages (σ × ℕ) ψ F (i + 1)
      (fun S => ModuleCat.isZero_iff_subsingleton.mpr
        (monicPrismaticBoundedSupportStage_tor_subsingleton D d f hf hpA v hv S i))
  let e : H.obj (ModuleCat.of L P) ≅ H.obj (colimit F) :=
    H.mapIso (deltaDivisionBoundedSupportColimitEvalIso E r).symm
  exact ModuleCat.subsingleton_of_isZero (hz.of_iso e)


/-- 概要：任意モニック族の全評価環の高次 Tor は零。
方針：既存の TorAlg の有限部分集合余極限保存を実評価図式に適用する。
規約：余極限交換の追加仮定を残さない。正次数は不要。
使われ方：BS Rem 7.15（著者版 p.62）の任意族の実残余係数拡大。 -/
theorem monicPrismaticEvaluation_tor_subsingleton
    (hf : ∀ t, (f t).Monic)
    (hpA : Function.Injective (fun z : A => (p : A) * z))
    (v : Aˣ) (hv : (v : A) = D.delta d) (i : ℕ) :
    letI := deltaDivisionSourceEvaluationAlgebra E r
    Subsingleton (SerrePositivity.TorAlg ψ (i + 1) P) := by
  let := torAlg_preservesFinsetColimits (σ × ℕ) ψ (i + 1)
  exact monicPrismaticEvaluation_tor_subsingleton_of_preservesBoundedSupportColimit
    D d f hf hpA v hv i inferInstance

local notation "β" => deltaDivisionSourceEval E r
local notation "Mψ" => baseChangeScalarModule ψ
local notation "Mβ" => baseChangeScalarModule β

/-- 概要：任意モニック族の実残余係数加群は全 β 評価射に関して Tor 非輪状。
方針：全評価環の TorAlg 消滅を通常 Tor 比較と対称性で移す。
規約：族全体の有限性も余極限交換仮定も不要。
使われ方：BS Rem 7.15（著者版 p.62）の標準導来 augmentation による比較。 -/
theorem monicPrismaticBoundedSupportResidueEval_torVanishing
    (hf : ∀ t, (f t).Monic)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    scalarExtensionTorVanishing β Mψ := by
  intro n hn
  cases n with
  | zero => exact (Nat.lt_irrefl 0 hn).elim
  | succ i =>
    let := deltaDivisionSourceEvaluationAlgebra E r
    let : Subsingleton (((ModuleCat.extendScalars ψ).leftDerived (i + 1)).obj Mβ) :=
      monicPrismaticEvaluation_tor_subsingleton D d f hf hpA v hv i
    have hz : IsZero (((ModuleCat.extendScalars ψ).leftDerived (i + 1)).obj Mβ) :=
      ModuleCat.isZero_of_subsingleton _
    have hH := (derivedModuleBaseChangeHomologyIso ψ (i + 1)).app Mβ
    have hzH := hH.isZero_iff.mpr hz
    have hzR := (ModuleCat.restrictScalars ψ).map_isZero hzH
    have hzT := ((derivedModuleBaseChangeTorIso ψ (i + 1)).app Mβ).isZero_iff.mp hzR
    exact ((torComm (i + 1) Mβ Mψ).toModuleIso).isZero_iff.mpr hzT

end SerrePositivity.BhattScholze.Andre
