module

public import SerrePositivity.BhattScholze.DeltaPDivisionFiniteEvaluationRegular
public import SerrePositivity.BhattScholze.DeltaDivisionSourceFiniteTor

/-! # 実自由δ射に沿う有限源グラフ商のTor

P=A{x}からL=A{z}、x↦p zへ基底変更した有限源商を、実評価関係Koszul複体で計算する。
有限商を全源評価環Aと取り違えない。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (y : A)
local notation "P₀" => RelativeFreeDeltaRing (R := A) σ
local notation "a₀" => fun _ : σ ↦ D.frobeniusLift y
local notation "α₀" => deltaDivisionSourceMap (σ := σ) D (p : A)

/-- 全深さ≤Nの、源評価核の具体的な有限グラフ列。 -/
def deltaPDivisionSourceGraphPrefix (N : ℕ) : Fin (N + 1) → P₀ :=
  fun i => deltaDivisionSourceGraphRelation D a₀ (default, i.val)

/-- 実源Pの有限グラフ関係商。全源評価環Aとはまだ同一視しない。 -/
abbrev DeltaPDivisionSourceFiniteQuotient (N : ℕ) :=
  P₀ ⧸ Ideal.span (Set.range (deltaPDivisionSourceGraphPrefix (σ := σ) D y N))

/-- 実源の各有限グラフ列のKoszul複体は、実有限源商の分解。 -/
theorem deltaPDivisionSourceGraphPrefix_isKoszulResolution (N : ℕ) :
    SerrePositivity.IsKoszulResolution (deltaPDivisionSourceGraphPrefix (σ := σ) D y N) := by
  apply deltaDivisionSourceGraph_fin_isKoszulResolution
  intro i j hij
  exact Fin.ext (congrArg Prod.snd hij)

/-- 実αに沿う実有限源商のTorと、終域の実評価関係Koszulホモロジーの比較。 -/
def deltaPDivisionSourceFiniteKoszulTorIso (N i : ℕ) :
    ((ModuleCat.extendScalars.{u, u, u} α₀).leftDerived i).obj
      (ModuleCat.of P₀ (DeltaPDivisionSourceFiniteQuotient (σ := σ) D y N)) ≅
      (SerrePositivity.koszulComplex (fun j : Fin (N + 1) =>
        deltaDivisionEvaluationRelation D (p : A) a₀ (default : σ) j.val)).homology (-(i : ℤ)) := by
  exact deltaDivisionSourceFiniteCoordinateKoszulTorIso D (p : A) a₀
    (fun j : Fin (N + 1) => (default, j.val))
    (fun _ _ hij => Fin.ext (congrArg Prod.snd hij)) i

/-- 正則一元入力では、実αに沿う有限源商の全正次数Torが零。 -/
theorem deltaPDivisionSourceFinite_tor_subsingleton
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p P₀ → ℕ → P₀))
    (v : Aˣ) (hv : (v : A) = D.delta (p : A))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) (N i : ℕ) :
    Subsingleton (SerrePositivity.TorAlg α₀ (i + 1)
      (DeltaPDivisionSourceFiniteQuotient (σ := σ) D y N)) := by
  exact deltaDivisionSourceFiniteCoordinate_tor_subsingleton D (p : A) a₀
    (fun j : Fin (N + 1) => (default, j.val))
    (fun _ _ hij => Fin.ext (congrArg Prod.snd hij))
    (deltaPDivisionFiniteEvaluation_isKoszulResolution D y hpA hg v hv hy N) i

end SerrePositivity.BhattScholze
