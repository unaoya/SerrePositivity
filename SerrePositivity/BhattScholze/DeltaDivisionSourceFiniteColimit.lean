module

public import SerrePositivity.BhattScholze.DeltaPDivisionSourceFiniteTor
public import SerrePositivity.BhattScholze.DeltaDivisionUnitDenominator
public import SerrePositivity.BhattScholze.DeltaDivisionSourceAlgebras
public import Mathlib.CategoryTheory.Functor.OfSequence

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

omit [Unique σ] in
private theorem evaluation_one (s : σ) (n : ℕ) :
    deltaDivisionEvaluationRelation D (1 : A) a₀ s n =
      deltaDivisionSourceGraphRelation D a₀ (s, n) := by
  have h := deltaDivisionSourceGraph_map D (1 : A) a₀ (s, n)
  rw [deltaDivisionSourceMap_one] at h
  exact h.symm

/-- 実源有限グラフイデアルは、分母1の有限δ関係イデアル。 -/
theorem deltaDivisionSourceFiniteIdeal_eq_one (N : ℕ) :
    K₀ N = deltaDivisionFiniteRelationIdeal D (1 : A) a₀ N := by
  rw [← deltaDivisionFiniteEvaluationIdeal_eq]
  change Ideal.span (Set.range (deltaPDivisionSourceGraphPrefix (σ := σ) D y N)) =
    Ideal.span (Set.range fun z : σ × Fin (N + 1) =>
      deltaDivisionEvaluationRelation D (1 : A) a₀ z.1 z.2.val)
  apply congrArg Ideal.span
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨(default, i), evaluation_one D y default i.val⟩
  · rintro ⟨⟨s, i⟩, rfl⟩
    have hs : s = (default : σ) := Subsingleton.elim _ _
    subst s
    exact ⟨i, (evaluation_one D y default i.val).symm⟩

/-- 実源評価核は、実有限グラフイデアルの上限。 -/
theorem deltaDivisionSourceEval_ker_eq_iSup_finite : RingHom.ker β₀ = ⨆ N, K₀ N := by
  rw [← deltaDivisionUnitDenominator_ideal, deltaDivision_deltaClosure_eq_iSup_finiteRelations]
  congr 1
  funext N
  exact (deltaDivisionSourceFiniteIdeal_eq_one D y N).symm

/-- 実源の有限グラフイデアルは深さについて単調。 -/
theorem deltaDivisionSourceFiniteIdeal_mono : Monotone K₀ := by
  intro N M h
  rw [deltaDivisionSourceFiniteIdeal_eq_one, deltaDivisionSourceFiniteIdeal_eq_one]
  exact deltaDivisionFiniteRelationIdeal_mono D (1 : A) a₀ h

private theorem finite_le_ker (N : ℕ) : K₀ N ≤ RingHom.ker β₀ := by
  rw [deltaDivisionSourceEval_ker_eq_iSup_finite]
  exact le_iSup (fun M : ℕ => Ideal.span
    (Set.range (deltaPDivisionSourceGraphPrefix (σ := σ) D y M))) N

/-- 評価環Aの源P代数構造は、実評価射βそのものから与える。 -/
@[instance_reducible] def deltaDivisionSourceEvalAlgebra : Algebra P₀ A :=
  deltaDivisionSourceEvaluationAlgebra D a₀

/-- 有限源商間の標準線形遷移射。 -/
def deltaDivisionSourceFiniteTransition (N : ℕ) : Q₀ N →ₗ[P₀] Q₀ (N + 1) :=
  Submodule.mapQ (K₀ N) (K₀ (N + 1)) LinearMap.id
    (by exact deltaDivisionSourceFiniteIdeal_mono D y (Nat.le_succ N))

/-- 標準遷移射は元の源環の標準商元を保つ。 -/
theorem deltaDivisionSourceFiniteTransition_mk (N : ℕ) (r : P₀) :
    deltaDivisionSourceFiniteTransition D y N (Ideal.Quotient.mk (K₀ N) r) =
      Ideal.Quotient.mk (K₀ (N + 1)) r :=
  Submodule.mapQ_apply _ _ _ r

/-- 実有限源商の具体的なP加群逐次図式。 -/
def deltaDivisionSourceFiniteModuleDiagram : ℕ ⥤ ModuleCat.{u} P₀ :=
  Functor.ofSequence (fun N => ModuleCat.ofHom (deltaDivisionSourceFiniteTransition D y N))

/-- 実源商図式の隣接射は、定義した標準商遷移射。 -/
theorem deltaDivisionSourceFiniteModuleDiagram_map_succ (N : ℕ) :
    (deltaDivisionSourceFiniteModuleDiagram (σ := σ) D y).map (homOfLE (Nat.le_succ N)) =
      ModuleCat.ofHom (deltaDivisionSourceFiniteTransition D y N) :=
  Functor.ofSequence_map_homOfLE_succ _ N

/-- βにより有限源商から実評価環Aへ降下する標準線形射。 -/
def deltaDivisionSourceFiniteEval (N : ℕ) :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    Q₀ N →ₗ[P₀] A := by
  letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
  exact Submodule.liftQ (K₀ N) (Algebra.linearMap P₀ A) (by exact finite_le_ker D y N)

/-- 有限源評価射は標準商元をβの実値へ送る。 -/
theorem deltaDivisionSourceFiniteEval_mk (N : ℕ) (r : P₀) :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    deltaDivisionSourceFiniteEval D y N (Ideal.Quotient.mk (K₀ N) r) = β₀ r := by
  let := deltaDivisionSourceEvalAlgebra (σ := σ) D y
  exact Submodule.liftQ_apply _ _ r

/-- 実評価環Aを頂点とする、有限源商の標準余錐。 -/
def deltaDivisionSourceFiniteEvalCocone :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    Cocone (deltaDivisionSourceFiniteModuleDiagram (σ := σ) D y) := by
  letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
  exact
    { pt := ModuleCat.of P₀ A
      ι := NatTrans.ofSequence (fun N => ModuleCat.ofHom (deltaDivisionSourceFiniteEval D y N))
        (by
          intro N
          rw [deltaDivisionSourceFiniteModuleDiagram_map_succ]
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro z
          obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
          change deltaDivisionSourceFiniteEval D y (N + 1)
            (deltaDivisionSourceFiniteTransition D y N (Ideal.Quotient.mk (K₀ N) r)) =
              deltaDivisionSourceFiniteEval D y N (Ideal.Quotient.mk (K₀ N) r)
          rw [deltaDivisionSourceFiniteTransition_mk,
            deltaDivisionSourceFiniteEval_mk, deltaDivisionSourceFiniteEval_mk]) }

private theorem cocone_mk_independent
    (c : Cocone (deltaDivisionSourceFiniteModuleDiagram (σ := σ) D y)) (N : ℕ) (r : P₀) :
    (c.ι.app N).hom (Ideal.Quotient.mk (K₀ N) r) =
      (c.ι.app 0).hom (Ideal.Quotient.mk (K₀ 0) r) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    have h := congrArg (fun f => f.hom (Ideal.Quotient.mk (K₀ N) r))
      (c.w (homOfLE (Nat.le_succ N)))
    rw [deltaDivisionSourceFiniteModuleDiagram_map_succ] at h
    change (c.ι.app (N + 1)).hom
      (deltaDivisionSourceFiniteTransition D y N (Ideal.Quotient.mk (K₀ N) r)) = _ at h
    rw [deltaDivisionSourceFiniteTransition_mk] at h
    exact h.trans ih

private theorem cocone_base_ker
    (c : Cocone (deltaDivisionSourceFiniteModuleDiagram (σ := σ) D y)) :
    RingHom.ker β₀ ≤ LinearMap.ker ((c.ι.app 0).hom.comp (Submodule.mkQ (K₀ 0))) := by
  rw [deltaDivisionSourceEval_ker_eq_iSup_finite]
  apply iSup_le
  intro N r hr
  change (c.ι.app 0).hom (Ideal.Quotient.mk (K₀ 0) r) = 0
  rw [← cocone_mk_independent D y c N r, Ideal.Quotient.eq_zero_iff_mem.mpr hr, map_zero]

/-- 実評価環Aは、源有限グラフ商の標準逐次colimitである。 -/
def deltaDivisionSourceFiniteEvalIsColimit :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    IsColimit (deltaDivisionSourceFiniteEvalCocone (σ := σ) D y) := by
  letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
  let b : P₀ →ₗ[P₀] A := Algebra.linearMap P₀ A
  let e := LinearMap.quotKerEquivOfSurjective b (deltaDivisionSourceEval_surjective D a₀)
  let desc (c : Cocone (deltaDivisionSourceFiniteModuleDiagram (σ := σ) D y)) : A →ₗ[P₀] c.pt :=
    (Submodule.liftQ (LinearMap.ker b)
      ((c.ι.app 0).hom.comp (Submodule.mkQ (K₀ 0))) (by exact cocone_base_ker D y c)).comp
        e.symm.toLinearMap
  have hdesc (c : Cocone (deltaDivisionSourceFiniteModuleDiagram (σ := σ) D y)) (r : P₀) :
      desc c (β₀ r) = (c.ι.app 0).hom (Ideal.Quotient.mk (K₀ 0) r) := by
    change Submodule.liftQ (LinearMap.ker b)
      ((c.ι.app 0).hom.comp (Submodule.mkQ (K₀ 0)))
        (by exact cocone_base_ker D y c) (e.symm (b r)) = _
    dsimp only [e]
    rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
    rfl
  exact
    { desc := fun c => ModuleCat.ofHom (desc c)
      fac := by
        intro c N
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro z
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
        change desc c (deltaDivisionSourceFiniteEval D y N (Ideal.Quotient.mk (K₀ N) r)) = _
        rw [deltaDivisionSourceFiniteEval_mk, hdesc]
        exact (cocone_mk_independent D y c N r).symm
      uniq := by
        intro c f hf
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro z
        obtain ⟨r, rfl⟩ := deltaDivisionSourceEval_surjective D a₀ z
        have h := congrArg (fun g => g.hom (Ideal.Quotient.mk (K₀ 0) r)) (hf 0)
        change f.hom (deltaDivisionSourceFiniteEval D y 0 (Ideal.Quotient.mk (K₀ 0) r)) = _ at h
        rw [deltaDivisionSourceFiniteEval_mk] at h
        exact h.trans (hdesc c r).symm }

/-- 実圏論的colimitと、βで作用する実評価環Aとの標準比較同型。 -/
def deltaDivisionSourceFiniteColimitEvalIso :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    colimit (deltaDivisionSourceFiniteModuleDiagram (σ := σ) D y) ≅ ModuleCat.of P₀ A := by
  letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
  exact (colimit.isColimit _).coconePointUniqueUpToIso (deltaDivisionSourceFiniteEvalIsColimit D y)

/-- 標準colimit比較同型は、各有限商からの標準β評価射を保つ。 -/
theorem deltaDivisionSourceFiniteColimitEvalIso_ι (N : ℕ) :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    colimit.ι (deltaDivisionSourceFiniteModuleDiagram (σ := σ) D y) N ≫
      (deltaDivisionSourceFiniteColimitEvalIso D y).hom =
        ModuleCat.ofHom (deltaDivisionSourceFiniteEval D y N) := by
  let := deltaDivisionSourceEvalAlgebra (σ := σ) D y
  exact IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit _)
    (deltaDivisionSourceFiniteEvalIsColimit D y) N

end SerrePositivity.BhattScholze
