module

public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.Division.DeltaPDivisionSourceFiniteTor
public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.Division.DeltaDivisionSourceEvaluationColimit

/-! # 源有限グラフ商の標準逐次極限

源評価射βの核が有限グラフイデアルの上限であることから、実評価環Aへの標準余錐の普遍性を示す。
Torとcolimitの交換はここでは仮定も結論もしない。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (y : A)
local notation "P₀" => RelativeFreeDeltaRing (R := A) σ
local notation "a₀" => fun _ : σ ↦ D.frobeniusLift y
local notation "β₀" => deltaDivisionSourceEval D a₀
local notation "K₀" => fun N : ℕ =>
  Ideal.span (Set.range (deltaPDivisionSourceGraphPrefix (σ := σ) D y N))
local notation "Q₀" => DeltaPDivisionSourceFiniteQuotient (σ := σ) D y

/-- 実源有限グラフイデアルは、分母1の有限δ関係イデアル。 -/
theorem deltaDivisionSourceFiniteIdeal_eq_one (N : ℕ) :
    K₀ N = deltaDivisionFiniteRelationIdeal D (1 : A) a₀ N :=
  deltaDivisionEvaluationSourceFiniteIdeal_eq_one D a₀ N

/-- 実源評価核は、実有限グラフイデアルの上限。 -/
theorem deltaDivisionSourceEval_ker_eq_iSup_finite : RingHom.ker β₀ = ⨆ N, K₀ N :=
  deltaDivisionEvaluationSourceEval_ker_eq_iSup_finite D a₀

/-- 実源の有限グラフイデアルは深さについて単調。 -/
theorem deltaDivisionSourceFiniteIdeal_mono : Monotone K₀ :=
  deltaDivisionEvaluationSourceFiniteIdeal_mono D a₀

/-- 評価環Aの源P代数構造は、実評価射βそのものから与える。 -/
@[instance_reducible] def deltaDivisionSourceEvalAlgebra : Algebra P₀ A :=
  deltaDivisionSourceEvaluationAlgebra D a₀

/-- 有限源商間の標準線形遷移射。 -/
def deltaDivisionSourceFiniteTransition (N : ℕ) : Q₀ N →ₗ[P₀] Q₀ (N + 1) :=
  deltaDivisionEvaluationSourceFiniteTransition D a₀ N

/-- 標準遷移射は元の源環の標準商元を保つ。 -/
theorem deltaDivisionSourceFiniteTransition_mk (N : ℕ) (r : P₀) :
    deltaDivisionSourceFiniteTransition D y N (Ideal.Quotient.mk (K₀ N) r) =
      Ideal.Quotient.mk (K₀ (N + 1)) r :=
  deltaDivisionEvaluationSourceFiniteTransition_mk D a₀ N r

/-- 実有限源商の具体的なP加群逐次図式。 -/
def deltaDivisionSourceFiniteModuleDiagram : ℕ ⥤ ModuleCat.{u} P₀ :=
  deltaDivisionEvaluationSourceFiniteModuleDiagram D a₀

/-- 実源商図式の隣接射は、定義した標準商遷移射。 -/
theorem deltaDivisionSourceFiniteModuleDiagram_map_succ (N : ℕ) :
    (deltaDivisionSourceFiniteModuleDiagram (σ := σ) D y).map (homOfLE (Nat.le_succ N)) =
      ModuleCat.ofHom (deltaDivisionSourceFiniteTransition D y N) :=
  deltaDivisionEvaluationSourceFiniteModuleDiagram_map_succ D a₀ N

/-- βにより有限源商から実評価環Aへ降下する標準線形射。 -/
def deltaDivisionSourceFiniteEval (N : ℕ) :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    Q₀ N →ₗ[P₀] A :=
  deltaDivisionEvaluationSourceFiniteEval D a₀ N

/-- 有限源評価射は標準商元をβの実値へ送る。 -/
theorem deltaDivisionSourceFiniteEval_mk (N : ℕ) (r : P₀) :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    deltaDivisionSourceFiniteEval D y N (Ideal.Quotient.mk (K₀ N) r) = β₀ r :=
  deltaDivisionEvaluationSourceFiniteEval_mk D a₀ N r

/-- 実評価環Aを頂点とする、有限源商の標準余錐。 -/
def deltaDivisionSourceFiniteEvalCocone :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    Cocone (deltaDivisionSourceFiniteModuleDiagram (σ := σ) D y) :=
  deltaDivisionEvaluationSourceFiniteEvalCocone D a₀

/-- 実評価環Aは、源有限グラフ商の標準逐次colimitである。 -/
def deltaDivisionSourceFiniteEvalIsColimit :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    IsColimit (deltaDivisionSourceFiniteEvalCocone (σ := σ) D y) :=
  deltaDivisionEvaluationSourceFiniteEvalIsColimit D a₀

/-- 実圏論的colimitと、βで作用する実評価環Aとの標準比較同型。 -/
def deltaDivisionSourceFiniteColimitEvalIso :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    colimit (deltaDivisionSourceFiniteModuleDiagram (σ := σ) D y) ≅ ModuleCat.of P₀ A :=
  deltaDivisionEvaluationSourceFiniteColimitEvalIso D a₀

/-- 標準colimit比較同型は、各有限商からの標準β評価射を保つ。 -/
theorem deltaDivisionSourceFiniteColimitEvalIso_ι (N : ℕ) :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    colimit.ι (deltaDivisionSourceFiniteModuleDiagram (σ := σ) D y) N ≫
      (deltaDivisionSourceFiniteColimitEvalIso D y).hom =
        ModuleCat.ofHom (deltaDivisionSourceFiniteEval D y N) :=
  deltaDivisionEvaluationSourceFiniteColimitEvalIso_ι D a₀ N

end SerrePositivity.BhattScholze
