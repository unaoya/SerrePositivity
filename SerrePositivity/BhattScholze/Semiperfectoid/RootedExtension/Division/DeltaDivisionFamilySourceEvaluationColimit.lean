module

public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.Division.DeltaDivisionFiniteFamilyEvaluation
public import SerrePositivity.BhattScholze.Delta.Division.Relations.DeltaDivisionUnitDenominator
public import SerrePositivity.BhattScholze.Delta.Division.Relations.DeltaDivisionSourceAlgebras
public import Mathlib.CategoryTheory.Functor.OfSequence

/-! # 有限根族評価の源有限グラフ商の標準逐次極限

源評価射βの核が有限グラフイデアルの上限であることから、実評価環Aへの標準余錐の普遍性を示す。
Torとcolimitの交換はここでは仮定も結論もしない。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (a : σ → A)
variable {m : ℕ} (s : Fin m ≃ σ)
local notation "P₀" => RelativeFreeDeltaRing (R := A) σ
local notation "a₀" => a
local notation "β₀" => deltaDivisionSourceEval D a₀
/-- 有限根族評価の深さ≤Nの具体的な源グラフ関係列。 -/
def deltaDivisionEvaluationSourceFamilyGraphPrefix (N : ℕ) :
    Fin (deltaDivisionFiniteFamilyCoordinates (s : Fin m → σ) N).length → P₀ :=
  fun i => deltaDivisionSourceGraphRelation D a
    ((deltaDivisionFiniteFamilyCoordinates (s : Fin m → σ) N).get i)

/-- 有限根族の深さN以下の実源グラフ商。 -/
abbrev DeltaDivisionEvaluationSourceFamilyQuotient (N : ℕ) :=
  DeltaDivisionSourceFiniteCoordinateQuotient D a
    (deltaDivisionFiniteFamilyCoordinates (s : Fin m → σ) N).get

local notation "K₀" => fun N : ℕ =>
  Ideal.span (Set.range (deltaDivisionEvaluationSourceFamilyGraphPrefix (σ := σ) D a s N))
local notation "Q₀" => DeltaDivisionEvaluationSourceFamilyQuotient (σ := σ) D a s

private theorem evaluation_one (s : σ) (n : ℕ) :
    deltaDivisionEvaluationRelation D (1 : A) a₀ s n =
      deltaDivisionSourceGraphRelation D a₀ (s, n) := by
  have h := deltaDivisionSourceGraph_map D (1 : A) a₀ (s, n)
  rw [deltaDivisionSourceMap_one] at h
  exact h.symm

/-- 実源有限グラフイデアルは、分母1の有限δ関係イデアル。 -/
theorem deltaDivisionEvaluationSourceFamilyIdeal_eq_one (N : ℕ) :
    K₀ N = deltaDivisionFiniteRelationIdeal D (1 : A) a₀ N := by
  rw [← deltaDivisionFiniteEvaluationIdeal_eq]
  change Ideal.span (Set.range (deltaDivisionEvaluationSourceFamilyGraphPrefix D a s N)) =
    Ideal.span (Set.range fun z : σ × Fin (N + 1) =>
      deltaDivisionEvaluationRelation D (1 : A) a₀ z.1 z.2.val)
  apply congrArg Ideal.span
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    obtain ⟨j, k, hk, he⟩ :=
      (deltaDivisionFiniteFamilyCoordinates_mem (s : Fin m → σ) N _).mp
        (List.get_mem _ i)
    refine ⟨(s j, ⟨k, by omega⟩), ?_⟩
    change deltaDivisionEvaluationRelation D 1 a (s j) k =
      deltaDivisionSourceGraphRelation D a _
    rw [← he]
    exact evaluation_one D a (s j) k
  · rintro ⟨⟨t, k⟩, rfl⟩
    obtain ⟨j, rfl⟩ := s.surjective t
    have hm : (s j, k.val) ∈ deltaDivisionFiniteFamilyCoordinates (s : Fin m → σ) N :=
      (deltaDivisionFiniteFamilyCoordinates_mem (s : Fin m → σ) N _).mpr
        ⟨j, k.val, by omega, rfl⟩
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hm
    refine ⟨i, ?_⟩
    change deltaDivisionSourceGraphRelation D a _ = _
    rw [hi]
    exact (evaluation_one D a (s j) k.val).symm

/-- 実源評価核は、実有限グラフイデアルの上限。 -/
theorem deltaDivisionEvaluationSourceEval_ker_eq_iSup_family : RingHom.ker β₀ = ⨆ N, K₀ N := by
  rw [← deltaDivisionUnitDenominator_ideal, deltaDivision_deltaClosure_eq_iSup_finiteRelations]
  congr 1
  funext N
  exact (deltaDivisionEvaluationSourceFamilyIdeal_eq_one D a s N).symm

/-- 実源の有限グラフイデアルは深さについて単調。 -/
theorem deltaDivisionEvaluationSourceFamilyIdeal_mono : Monotone K₀ := by
  intro N M h
  rw [deltaDivisionEvaluationSourceFamilyIdeal_eq_one,
    deltaDivisionEvaluationSourceFamilyIdeal_eq_one]
  exact deltaDivisionFiniteRelationIdeal_mono D (1 : A) a₀ h

private theorem finite_le_ker (N : ℕ) : K₀ N ≤ RingHom.ker β₀ := by
  rw [deltaDivisionEvaluationSourceEval_ker_eq_iSup_family D a s]
  exact le_iSup (fun M : ℕ => Ideal.span
    (Set.range (deltaDivisionEvaluationSourceFamilyGraphPrefix (σ := σ) D a s M))) N

/-- 有限源商間の標準線形遷移射。 -/
def deltaDivisionEvaluationSourceFamilyTransition (N : ℕ) : Q₀ N →ₗ[P₀] Q₀ (N + 1) :=
  Submodule.mapQ (K₀ N) (K₀ (N + 1)) LinearMap.id
    (by exact deltaDivisionEvaluationSourceFamilyIdeal_mono D a s (Nat.le_succ N))

/-- 標準遷移射は元の源環の標準商元を保つ。 -/
theorem deltaDivisionEvaluationSourceFamilyTransition_mk (N : ℕ) (r : P₀) :
    deltaDivisionEvaluationSourceFamilyTransition D a s N (Ideal.Quotient.mk (K₀ N) r) =
      Ideal.Quotient.mk (K₀ (N + 1)) r :=
  Submodule.mapQ_apply _ _ _ r

/-- 実有限源商の具体的なP加群逐次図式。 -/
def deltaDivisionEvaluationSourceFamilyModuleDiagram : ℕ ⥤ ModuleCat.{u} P₀ :=
  Functor.ofSequence
    (fun N => ModuleCat.ofHom (deltaDivisionEvaluationSourceFamilyTransition D a s N))

/-- 実源商図式の隣接射は、定義した標準商遷移射。 -/
theorem deltaDivisionEvaluationSourceFamilyModuleDiagram_map_succ (N : ℕ) :
    (deltaDivisionEvaluationSourceFamilyModuleDiagram (σ := σ) D a s).map
        (homOfLE (Nat.le_succ N)) =
      ModuleCat.ofHom (deltaDivisionEvaluationSourceFamilyTransition D a s N) :=
  Functor.ofSequence_map_homOfLE_succ _ N

/-- βにより有限源商から実評価環Aへ降下する標準線形射。 -/
def deltaDivisionEvaluationSourceFamilyEval (N : ℕ) :
    letI := deltaDivisionSourceEvaluationAlgebra D a₀
    Q₀ N →ₗ[P₀] A := by
  letI := deltaDivisionSourceEvaluationAlgebra D a₀
  exact Submodule.liftQ (K₀ N) (Algebra.linearMap P₀ A) (by exact finite_le_ker D a s N)

/-- 有限源評価射は標準商元をβの実値へ送る。 -/
theorem deltaDivisionEvaluationSourceFamilyEval_mk (N : ℕ) (r : P₀) :
    letI := deltaDivisionSourceEvaluationAlgebra D a₀
    deltaDivisionEvaluationSourceFamilyEval D a s N (Ideal.Quotient.mk (K₀ N) r) = β₀ r := by
  let := deltaDivisionSourceEvaluationAlgebra D a₀
  exact Submodule.liftQ_apply _ _ r

/-- 実評価環Aを頂点とする、有限源商の標準余錐。 -/
def deltaDivisionEvaluationSourceFamilyEvalCocone :
    letI := deltaDivisionSourceEvaluationAlgebra D a₀
    Cocone (deltaDivisionEvaluationSourceFamilyModuleDiagram (σ := σ) D a s) := by
  letI := deltaDivisionSourceEvaluationAlgebra D a₀
  exact
    { pt := ModuleCat.of P₀ A
      ι := NatTrans.ofSequence
        (fun N => ModuleCat.ofHom (deltaDivisionEvaluationSourceFamilyEval D a s N))
        (by
          intro N
          rw [deltaDivisionEvaluationSourceFamilyModuleDiagram_map_succ]
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro z
          obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
          change deltaDivisionEvaluationSourceFamilyEval D a s (N + 1)
            (deltaDivisionEvaluationSourceFamilyTransition D a s N (Ideal.Quotient.mk (K₀ N) r)) =
              deltaDivisionEvaluationSourceFamilyEval D a s N (Ideal.Quotient.mk (K₀ N) r)
          rw [deltaDivisionEvaluationSourceFamilyTransition_mk,
            deltaDivisionEvaluationSourceFamilyEval_mk,
            deltaDivisionEvaluationSourceFamilyEval_mk]) }

private theorem cocone_mk_independent
    (c : Cocone (deltaDivisionEvaluationSourceFamilyModuleDiagram (σ := σ) D a s))
    (N : ℕ) (r : P₀) :
    (c.ι.app N).hom (Ideal.Quotient.mk (K₀ N) r) =
      (c.ι.app 0).hom (Ideal.Quotient.mk (K₀ 0) r) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    have h := congrArg (fun f => f.hom (Ideal.Quotient.mk (K₀ N) r))
      (c.w (homOfLE (Nat.le_succ N)))
    rw [deltaDivisionEvaluationSourceFamilyModuleDiagram_map_succ] at h
    change (c.ι.app (N + 1)).hom
      (deltaDivisionEvaluationSourceFamilyTransition D a s N (Ideal.Quotient.mk (K₀ N) r)) = _ at h
    rw [deltaDivisionEvaluationSourceFamilyTransition_mk] at h
    exact h.trans ih

private theorem cocone_base_ker
    (c : Cocone (deltaDivisionEvaluationSourceFamilyModuleDiagram (σ := σ) D a s)) :
    RingHom.ker β₀ ≤ LinearMap.ker ((c.ι.app 0).hom.comp (Submodule.mkQ (K₀ 0))) := by
  rw [deltaDivisionEvaluationSourceEval_ker_eq_iSup_family D a s]
  apply iSup_le
  intro N r hr
  change (c.ι.app 0).hom (Ideal.Quotient.mk (K₀ 0) r) = 0
  rw [← cocone_mk_independent D a s c N r, Ideal.Quotient.eq_zero_iff_mem.mpr hr, map_zero]

/-- 実評価環Aは、源有限グラフ商の標準逐次colimitである。 -/
def deltaDivisionEvaluationSourceFamilyEvalIsColimit :
    letI := deltaDivisionSourceEvaluationAlgebra D a₀
    IsColimit (deltaDivisionEvaluationSourceFamilyEvalCocone (σ := σ) D a s) := by
  letI := deltaDivisionSourceEvaluationAlgebra D a₀
  let b : P₀ →ₗ[P₀] A := Algebra.linearMap P₀ A
  let e := LinearMap.quotKerEquivOfSurjective b (deltaDivisionSourceEval_surjective D a₀)
  let desc (c : Cocone (deltaDivisionEvaluationSourceFamilyModuleDiagram (σ := σ) D a s)) :
      A →ₗ[P₀] c.pt :=
    (Submodule.liftQ (LinearMap.ker b)
      ((c.ι.app 0).hom.comp (Submodule.mkQ (K₀ 0))) (by exact cocone_base_ker D a s c)).comp
        e.symm.toLinearMap
  have hdesc (c : Cocone (deltaDivisionEvaluationSourceFamilyModuleDiagram (σ := σ) D a s))
      (r : P₀) :
      desc c (β₀ r) = (c.ι.app 0).hom (Ideal.Quotient.mk (K₀ 0) r) := by
    change Submodule.liftQ (LinearMap.ker b)
      ((c.ι.app 0).hom.comp (Submodule.mkQ (K₀ 0)))
        (by exact cocone_base_ker D a s c) (e.symm (b r)) = _
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
        change desc c
          (deltaDivisionEvaluationSourceFamilyEval D a s N (Ideal.Quotient.mk (K₀ N) r)) = _
        rw [deltaDivisionEvaluationSourceFamilyEval_mk, hdesc]
        exact (cocone_mk_independent D a s c N r).symm
      uniq := by
        intro c f hf
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro z
        obtain ⟨r, rfl⟩ := deltaDivisionSourceEval_surjective D a₀ z
        have h := congrArg (fun g => g.hom (Ideal.Quotient.mk (K₀ 0) r)) (hf 0)
        change f.hom
          (deltaDivisionEvaluationSourceFamilyEval D a s 0 (Ideal.Quotient.mk (K₀ 0) r)) = _ at h
        rw [deltaDivisionEvaluationSourceFamilyEval_mk] at h
        exact h.trans (hdesc c r).symm }

/-- 実圏論的colimitと、βで作用する実評価環Aとの標準比較同型。 -/
def deltaDivisionEvaluationSourceFamilyColimitEvalIso :
    letI := deltaDivisionSourceEvaluationAlgebra D a₀
    colimit (deltaDivisionEvaluationSourceFamilyModuleDiagram (σ := σ) D a s) ≅
      ModuleCat.of P₀ A := by
  letI := deltaDivisionSourceEvaluationAlgebra D a₀
  exact (colimit.isColimit _).coconePointUniqueUpToIso
    (deltaDivisionEvaluationSourceFamilyEvalIsColimit D a s)

/-- 標準colimit比較同型は、各有限商からの標準β評価射を保つ。 -/
theorem deltaDivisionEvaluationSourceFamilyColimitEvalIso_ι (N : ℕ) :
    letI := deltaDivisionSourceEvaluationAlgebra D a₀
    colimit.ι (deltaDivisionEvaluationSourceFamilyModuleDiagram (σ := σ) D a s) N ≫
      (deltaDivisionEvaluationSourceFamilyColimitEvalIso D a s).hom =
        ModuleCat.ofHom (deltaDivisionEvaluationSourceFamilyEval D a s N) := by
  let := deltaDivisionSourceEvaluationAlgebra D a₀
  exact IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit _)
    (deltaDivisionEvaluationSourceFamilyEvalIsColimit D a s) N

end SerrePositivity.BhattScholze
