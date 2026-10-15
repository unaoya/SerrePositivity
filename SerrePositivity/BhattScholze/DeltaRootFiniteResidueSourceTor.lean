module

public import SerrePositivity.BhattScholze.DeltaDivisionMappedEvaluationKoszul
public import SerrePositivity.BhattScholze.DeltaRootFiniteResidueKoszul

/-! # 一元根添加の全有限深さの実残余評価Koszul分解と源Tor

実自由δ射αの後にmod(p,d)商射を合成した通常射を使う。
全源評価環のTorや実導来完備化後の完全忠実平坦性はここでは結論しない。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (d : A) (b : σ → A)
local notation "P₀" => MvPolynomial σ A
local notation "L₀" => RelativeFreeDeltaRing (R := P₀) σ
local notation "E₀" => polynomialRankOneDeltaStructure σ D
local notation "c₀" => deltaRootRelationFamily (p := p) b
local notation "K₀" => Ideal.span {(p : L₀), MvPolynomial.C (MvPolynomial.C d)}
local notation "q₀" => Ideal.Quotient.mk K₀
local notation "α₀" => deltaDivisionSourceMap (σ := σ) E₀ (MvPolynomial.C d)

/-- 一元根添加の全有限深さの実評価列は、実mod(p,d)商上でKoszul分解を与える。 -/
theorem deltaRootFiniteResidueEvaluation_isKoszulResolution
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (v : Aˣ) (hv : (v : A) = D.delta d) (N : ℕ) :
    SerrePositivity.IsKoszulResolution (fun i : Fin (N + 1) =>
      q₀ (deltaDivisionEvaluationRelation E₀ (MvPolynomial.C d) c₀ default i.val)) :=
  deltaDivisionMappedEvaluation_isKoszulResolution E₀ (MvPolynomial.C d) c₀ q₀
    (deltaRootFiniteResidueRelations_isWeaklyRegular D d b hpA hg v hv) N

/-- 実残余自由δ射に沿う全有限源グラフ商のTorを、実残余評価Koszulホモロジーで計算する。 -/
def deltaRootFiniteResidueSourceKoszulTorIso (N i : ℕ) :
    ((ModuleCat.extendScalars.{u, u, u} ((q₀).comp α₀)).leftDerived i).obj
      (ModuleCat.of L₀ (DeltaDivisionSourceFiniteCoordinateQuotient E₀ c₀
        (fun j : Fin (N + 1) => (default, j.val)))) ≅
      (SerrePositivity.koszulComplex (fun j : Fin (N + 1) =>
        q₀ (deltaDivisionEvaluationRelation E₀ (MvPolynomial.C d) c₀ default j.val))).homology
          (-(i : ℤ)) := by
  have e := SerrePositivity.torAlgKoszulIso ((q₀).comp α₀)
    (fun j : Fin (N + 1) => deltaDivisionSourceGraphRelation E₀ c₀ (default, j.val))
    (deltaDivisionSourceGraph_fin_isKoszulResolution E₀ c₀
      (fun j : Fin (N + 1) => (default, j.val))
      (fun _ _ hij => Fin.ext (congrArg Prod.snd hij))) i
  have he : ((q₀).comp α₀) ∘
      (fun j : Fin (N + 1) => deltaDivisionSourceGraphRelation E₀ c₀ (default, j.val)) =
      (fun j : Fin (N + 1) =>
        q₀ (deltaDivisionEvaluationRelation E₀ (MvPolynomial.C d) c₀ default j.val)) := by
    funext j
    exact congrArg q₀ (deltaDivisionSourceGraph_map E₀ (MvPolynomial.C d) c₀ (default, j.val))
  rw [he] at e
  exact e

/-- 明示した正規化入力の下、実残余自由δ射に沿う任意有限源商の全正次数Torは零。 -/
theorem deltaRootFiniteResidueSource_tor_subsingleton
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (v : Aˣ) (hv : (v : A) = D.delta d) (N i : ℕ) :
    Subsingleton (SerrePositivity.TorAlg ((q₀).comp α₀) (i + 1)
      (DeltaDivisionSourceFiniteCoordinateQuotient E₀ c₀
        (fun j : Fin (N + 1) => (default, j.val)))) := by
  have hr := deltaRootFiniteResidueEvaluation_isKoszulResolution D d b hpA hg v hv N
  have hz := hr.isZero (-((i + 1 : ℕ) : ℤ)) (by omega)
  have ht := hz.of_iso (deltaRootFiniteResidueSourceKoszulTorIso D d b N (i + 1))
  exact ModuleCat.subsingleton_of_isZero ht

end SerrePositivity.BhattScholze
