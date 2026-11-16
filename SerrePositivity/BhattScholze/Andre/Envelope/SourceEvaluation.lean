module

public import SerrePositivity.BhattScholze.Delta.Division.Source
public import SerrePositivity.BhattScholze.Andre.Envelope.RootRelation
public import Mathlib.CategoryTheory.Functor.OfSequence
public import SerrePositivity.HomologicalAlgebra.TorSequentialColimits
public import SerrePositivity.HomologicalAlgebra.FiniteSupQuotientColimit
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.Data.Finset.Prod

/-!
# 源グラフ商と評価環の余極限・Tor

## 概要
源 δ 評価核の有限グラフ Koszul 分解、一般の除数・任意有限 δ 座標の源グラフ商の Tor、任意一元評価の源有限グラフ商の逐次極限と Tor の移送、任意根族の評価核の有限座標支持と有限座標商の余極限、有界 δ 深さの評価図式。
BS 著者版 Proposition 3.13 の包の正則性に関わる、源グラフ商と評価環の Tor を計算する。

## 方針
構成ごとに補題をまとめ、各節で共通の仮定を明示する。

## 規約
係数環・素数・正則性の仮定は各宣言で明示する。

## 使われ方
`Envelope/FamilyEvaluation`、`Envelope/JetRegularity`、`Envelope/PDivision`、`Envelope/PDivisionSource`、`Envelope/RootResidueKoszul`、`Envelope/RootSource`、`PowerRootEnvelope/Unconditional/Residue`、`RootEnvelope/Source`、`Variants/Auxiliary`。
-/

universe u v

/-! ## 源δ評価核の有限グラフKoszul分解

任意の異なる有限δ座標を扱い、係数環のp正則性・ghost単射・完備性は要求しない。
指数1の商表示は既存APIを用い、正則性はモニック一次式から示す。
-/

@[expose] public noncomputable section DeltaDivisionSourceGraphKoszul

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 源δ評価射の座標グラフ関係。 -/
def Andre.deltaDivisionSourceGraphRelation (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A) (a : σ → A) (z : σ × ℕ) :
    _root_.SerrePositivity.BhattScholze.RelativeFreeDeltaRing (R := A) σ :=
  MvPolynomial.X z - MvPolynomial.C (D.delta^[z.2] (a z.1))

/-- 任意の異なる有限δ座標の源グラフ関係は弱正則列。 -/
theorem Andre.deltaDivisionSourceGraph_fin_isWeaklyRegular (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A) (a : σ → A)
    {m : ℕ} (s : Fin m → σ × ℕ) (hs : Function.Injective s) :
    RingTheory.Sequence.IsWeaklyRegular (_root_.SerrePositivity.BhattScholze.RelativeFreeDeltaRing (R := A) σ)
      (List.ofFn fun i => _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceGraphRelation D a (s i)) := by
  simpa only [List.map_ofFn, Function.comp_def, _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceGraphRelation,
    _root_.SerrePositivity.BhattScholze.Andre.deltaRootRelationFamily, pow_one] using
    _root_.SerrePositivity.BhattScholze.Andre.deltaRootRelation_list_isWeaklyRegular_of_ne_zero (p := 1) one_ne_zero
      (fun z : σ × ℕ => D.delta^[z.2] (a z.1))
      (List.ofFn s) (List.nodup_ofFn_ofInjective hs)

/-- 異なる有限δ座標の源グラフKoszul複体は、その実通常商の分解。 -/
theorem Andre.deltaDivisionSourceGraph_fin_isKoszulResolution (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A) (a : σ → A)
    {m : ℕ} (s : Fin m → σ × ℕ) (hs : Function.Injective s) :
    SerrePositivity.IsKoszulResolution (fun i => _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceGraphRelation D a (s i)) :=
  SerrePositivity.isKoszulResolution_of_isWeaklyRegular _
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceGraph_fin_isWeaklyRegular D a s hs)

/-- 源グラフ関係のαに沿う通常像は、実終域上の評価関係。 -/
theorem Andre.deltaDivisionSourceGraph_map (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A) (d : A) (a : σ → A)
    (z : σ × ℕ) :
    _root_.SerrePositivity.BhattScholze.deltaDivisionSourceMap D d (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceGraphRelation D a z) =
      _root_.SerrePositivity.BhattScholze.deltaDivisionEvaluationRelation D d a z.1 z.2 :=
  _root_.SerrePositivity.BhattScholze.deltaDivisionSourceMap_graphRelation D d a z.1 z.2

end SerrePositivity.BhattScholze

end DeltaDivisionSourceGraphKoszul

/-! ## 一般除数・任意有限δ座標の源グラフ商のTor

実自由δ射 x_s ↦ d z_s に沿う有限源商のTorを、終域の評価関係の
Koszulホモロジーで計算する。全源評価環への移行は含まない。
-/

@[expose] public noncomputable section DeltaDivisionSourceFiniteTor

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open _root_.CategoryTheory
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (c : σ → A)
local notation "P₀" => RelativeFreeDeltaRing (R := A) σ

/-- 指定した有限δ座標の源グラフ関係による実通常商。 -/
abbrev Andre.DeltaDivisionSourceFiniteCoordinateQuotient {m : ℕ} (s : Fin m → σ × ℕ) :=
  P₀ ⧸ Ideal.span (Set.range fun i => _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceGraphRelation D c (s i))

/-- 一般自由δ射に沿う有限源商のTorは、実終域の評価関係Koszulホモロジー。 -/
def Andre.deltaDivisionSourceFiniteCoordinateKoszulTorIso {m : ℕ} (s : Fin m → σ × ℕ)
    (hs : Function.Injective s) (i : ℕ) :
    ((ModuleCat.extendScalars.{u, u, u} (_root_.SerrePositivity.BhattScholze.deltaDivisionSourceMap (σ := σ) D d)).leftDerived i).obj
      (ModuleCat.of P₀ (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionSourceFiniteCoordinateQuotient D c s)) ≅
      (SerrePositivity.koszulComplex (fun j =>
        _root_.SerrePositivity.BhattScholze.deltaDivisionEvaluationRelation D d c (s j).1 (s j).2)).homology (-(i : ℤ)) := by
  have e := SerrePositivity.torAlgKoszulIso (_root_.SerrePositivity.BhattScholze.deltaDivisionSourceMap (σ := σ) D d)
    (fun j => _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceGraphRelation D c (s j))
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceGraph_fin_isKoszulResolution D c s hs) i
  have he : (_root_.SerrePositivity.BhattScholze.deltaDivisionSourceMap (σ := σ) D d) ∘
      (fun j => _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceGraphRelation D c (s j)) =
      (fun j => _root_.SerrePositivity.BhattScholze.deltaDivisionEvaluationRelation D d c (s j).1 (s j).2) := by
    funext j
    exact _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceGraph_map D d c (s j)
  rw [he] at e
  exact e

/-- 終域の有限評価関係がKoszul分解を与える場合、実有限源商の全正次数Torは零。 -/
theorem Andre.deltaDivisionSourceFiniteCoordinate_tor_subsingleton {m : ℕ}
    (s : Fin m → σ × ℕ) (hs : Function.Injective s)
    (hr : SerrePositivity.IsKoszulResolution (fun j =>
      _root_.SerrePositivity.BhattScholze.deltaDivisionEvaluationRelation D d c (s j).1 (s j).2)) (i : ℕ) :
    Subsingleton (SerrePositivity.TorAlg (_root_.SerrePositivity.BhattScholze.deltaDivisionSourceMap (σ := σ) D d) (i + 1)
      (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionSourceFiniteCoordinateQuotient D c s)) := by
  have hz := hr.isZero (-((i + 1 : ℕ) : ℤ)) (by omega)
  have ht := hz.of_iso (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceFiniteCoordinateKoszulTorIso D d c s hs (i + 1))
  exact ModuleCat.subsingleton_of_isZero ht

end SerrePositivity.BhattScholze

end DeltaDivisionSourceFiniteTor

/-! ## 任意一元評価の源有限グラフ商の標準逐次極限

源評価射βの核が有限グラフイデアルの上限であることから、実評価環Aへの標準余錐の普遍性を示す。
Torとcolimitの交換はここでは仮定も結論もしない。
-/

@[expose] public noncomputable section DeltaDivisionSourceEvaluationColimit

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open _root_.CategoryTheory _root_.CategoryTheory.Limits
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (a : σ → A)
local notation "P₀" => RelativeFreeDeltaRing (R := A) σ
local notation "a₀" => a
local notation "β₀" => deltaDivisionSourceEval D a₀
/-- 任意一元評価の深さ≤Nの具体的な源グラフ関係列。 -/
def Andre.deltaDivisionEvaluationSourceGraphPrefix (N : ℕ) : Fin (N + 1) → P₀ :=
  fun i => _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceGraphRelation D a (default, i.val)

/-- 任意一元評価の深さ≤Nの実源グラフ商。 -/
abbrev Andre.DeltaDivisionEvaluationSourceFiniteQuotient (N : ℕ) :=
  _root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionSourceFiniteCoordinateQuotient D a
    (fun i : Fin (N + 1) => (default, i.val))

local notation "K₀" => fun N : ℕ =>
  Ideal.span (Set.range (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceGraphPrefix (σ := σ) D a N))
local notation "Q₀" => _root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionEvaluationSourceFiniteQuotient (σ := σ) D a

omit [Unique σ] in
private theorem Andre.evaluation_one (s : σ) (n : ℕ) :
    _root_.SerrePositivity.BhattScholze.deltaDivisionEvaluationRelation D (1 : A) a₀ s n =
      _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceGraphRelation D a₀ (s, n) := by
  have h := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceGraph_map D (1 : A) a₀ (s, n)
  rw [_root_.SerrePositivity.BhattScholze.deltaDivisionSourceMap_one] at h
  exact h.symm

/-- 実源有限グラフイデアルは、分母1の有限δ関係イデアル。 -/
theorem Andre.deltaDivisionEvaluationSourceFiniteIdeal_eq_one (N : ℕ) :
    K₀ N = _root_.SerrePositivity.BhattScholze.deltaDivisionFiniteRelationIdeal D (1 : A) a₀ N := by
  rw [← _root_.SerrePositivity.BhattScholze.deltaDivisionFiniteEvaluationIdeal_eq]
  change Ideal.span (Set.range (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceGraphPrefix (σ := σ) D a N)) =
    Ideal.span (Set.range fun z : σ × Fin (N + 1) =>
      _root_.SerrePositivity.BhattScholze.deltaDivisionEvaluationRelation D (1 : A) a₀ z.1 z.2.val)
  apply congrArg Ideal.span
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨(default, i), _root_.SerrePositivity.BhattScholze.Andre.evaluation_one D a default i.val⟩
  · rintro ⟨⟨s, i⟩, rfl⟩
    have hs : s = (default : σ) := Subsingleton.elim _ _
    subst s
    exact ⟨i, (_root_.SerrePositivity.BhattScholze.Andre.evaluation_one D a default i.val).symm⟩

/-- 実源評価核は、実有限グラフイデアルの上限。 -/
theorem Andre.deltaDivisionEvaluationSourceEval_ker_eq_iSup_finite : RingHom.ker β₀ = ⨆ N, K₀ N := by
  rw [← _root_.SerrePositivity.BhattScholze.deltaDivisionUnitDenominator_ideal, _root_.SerrePositivity.BhattScholze.deltaDivision_deltaClosure_eq_iSup_finiteRelations]
  congr 1
  funext N
  exact (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFiniteIdeal_eq_one D a N).symm

/-- 実源の有限グラフイデアルは深さについて単調。 -/
theorem Andre.deltaDivisionEvaluationSourceFiniteIdeal_mono : Monotone K₀ := by
  intro N M h
  rw [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFiniteIdeal_eq_one,
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFiniteIdeal_eq_one]
  exact _root_.SerrePositivity.BhattScholze.deltaDivisionFiniteRelationIdeal_mono D (1 : A) a₀ h

private theorem Andre.finite_le_ker (N : ℕ) : K₀ N ≤ RingHom.ker β₀ := by
  rw [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceEval_ker_eq_iSup_finite]
  exact le_iSup (fun M : ℕ => Ideal.span
    (Set.range (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceGraphPrefix (σ := σ) D a M))) N

/-- 有限源商間の標準線形遷移射。 -/
def Andre.deltaDivisionEvaluationSourceFiniteTransition (N : ℕ) : Q₀ N →ₗ[P₀] Q₀ (N + 1) :=
  Submodule.mapQ (K₀ N) (K₀ (N + 1)) LinearMap.id
    (by exact _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFiniteIdeal_mono D a (Nat.le_succ N))

/-- 標準遷移射は元の源環の標準商元を保つ。 -/
theorem Andre.deltaDivisionEvaluationSourceFiniteTransition_mk (N : ℕ) (r : P₀) :
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFiniteTransition D a N (Ideal.Quotient.mk (K₀ N) r) =
      Ideal.Quotient.mk (K₀ (N + 1)) r :=
  Submodule.mapQ_apply _ _ _ r

/-- 実有限源商の具体的なP加群逐次図式。 -/
def Andre.deltaDivisionEvaluationSourceFiniteModuleDiagram : ℕ ⥤ ModuleCat.{u} P₀ :=
  Functor.ofSequence
    (fun N => ModuleCat.ofHom (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFiniteTransition D a N))

/-- 実源商図式の隣接射は、定義した標準商遷移射。 -/
theorem Andre.deltaDivisionEvaluationSourceFiniteModuleDiagram_map_succ (N : ℕ) :
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFiniteModuleDiagram (σ := σ) D a).map (homOfLE (Nat.le_succ N)) =
      ModuleCat.ofHom (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFiniteTransition D a N) :=
  Functor.ofSequence_map_homOfLE_succ _ N

/-- βにより有限源商から実評価環Aへ降下する標準線形射。 -/
def Andre.deltaDivisionEvaluationSourceFiniteEval (N : ℕ) :
    letI := _root_.SerrePositivity.BhattScholze.deltaDivisionSourceEvaluationAlgebra D a₀
    Q₀ N →ₗ[P₀] A := by
  letI := _root_.SerrePositivity.BhattScholze.deltaDivisionSourceEvaluationAlgebra D a₀
  exact Submodule.liftQ (K₀ N) (Algebra.linearMap P₀ A) (by exact _root_.SerrePositivity.BhattScholze.Andre.finite_le_ker D a N)

/-- 有限源評価射は標準商元をβの実値へ送る。 -/
theorem Andre.deltaDivisionEvaluationSourceFiniteEval_mk (N : ℕ) (r : P₀) :
    letI := _root_.SerrePositivity.BhattScholze.deltaDivisionSourceEvaluationAlgebra D a₀
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFiniteEval D a N (Ideal.Quotient.mk (K₀ N) r) = β₀ r := by
  let := _root_.SerrePositivity.BhattScholze.deltaDivisionSourceEvaluationAlgebra D a₀
  exact Submodule.liftQ_apply _ _ r

/-- 実評価環Aを頂点とする、有限源商の標準余錐。 -/
def Andre.deltaDivisionEvaluationSourceFiniteEvalCocone :
    letI := _root_.SerrePositivity.BhattScholze.deltaDivisionSourceEvaluationAlgebra D a₀
    Cocone (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFiniteModuleDiagram (σ := σ) D a) := by
  letI := _root_.SerrePositivity.BhattScholze.deltaDivisionSourceEvaluationAlgebra D a₀
  exact
    { pt := ModuleCat.of P₀ A
      ι := NatTrans.ofSequence
        (fun N => ModuleCat.ofHom (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFiniteEval D a N))
        (by
          intro N
          rw [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFiniteModuleDiagram_map_succ]
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro z
          obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
          change _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFiniteEval D a (N + 1)
            (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFiniteTransition D a N (Ideal.Quotient.mk (K₀ N) r)) =
              _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFiniteEval D a N (Ideal.Quotient.mk (K₀ N) r)
          rw [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFiniteTransition_mk,
            _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFiniteEval_mk,
            _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFiniteEval_mk]) }

private theorem Andre.cocone_mk_independent
    (c : Cocone (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFiniteModuleDiagram (σ := σ) D a)) (N : ℕ) (r : P₀) :
    (c.ι.app N).hom (Ideal.Quotient.mk (K₀ N) r) =
      (c.ι.app 0).hom (Ideal.Quotient.mk (K₀ 0) r) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    have h := congrArg (fun f => f.hom (Ideal.Quotient.mk (K₀ N) r))
      (c.w (homOfLE (Nat.le_succ N)))
    rw [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFiniteModuleDiagram_map_succ] at h
    change (c.ι.app (N + 1)).hom
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFiniteTransition D a N (Ideal.Quotient.mk (K₀ N) r)) = _ at h
    rw [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFiniteTransition_mk] at h
    exact h.trans ih

private theorem Andre.cocone_base_ker
    (c : Cocone (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFiniteModuleDiagram (σ := σ) D a)) :
    RingHom.ker β₀ ≤ LinearMap.ker ((c.ι.app 0).hom.comp (Submodule.mkQ (K₀ 0))) := by
  rw [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceEval_ker_eq_iSup_finite]
  apply iSup_le
  intro N r hr
  change (c.ι.app 0).hom (Ideal.Quotient.mk (K₀ 0) r) = 0
  rw [← _root_.SerrePositivity.BhattScholze.Andre.cocone_mk_independent D a c N r, Ideal.Quotient.eq_zero_iff_mem.mpr hr, map_zero]

/-- 実評価環Aは、源有限グラフ商の標準逐次colimitである。 -/
def Andre.deltaDivisionEvaluationSourceFiniteEvalIsColimit :
    letI := _root_.SerrePositivity.BhattScholze.deltaDivisionSourceEvaluationAlgebra D a₀
    IsColimit (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFiniteEvalCocone (σ := σ) D a) := by
  letI := _root_.SerrePositivity.BhattScholze.deltaDivisionSourceEvaluationAlgebra D a₀
  let b : P₀ →ₗ[P₀] A := Algebra.linearMap P₀ A
  let e := LinearMap.quotKerEquivOfSurjective b (_root_.SerrePositivity.BhattScholze.deltaDivisionSourceEval_surjective D a₀)
  let desc (c : Cocone (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFiniteModuleDiagram (σ := σ) D a)) :
      A →ₗ[P₀] c.pt :=
    (Submodule.liftQ (LinearMap.ker b)
      ((c.ι.app 0).hom.comp (Submodule.mkQ (K₀ 0))) (by exact _root_.SerrePositivity.BhattScholze.Andre.cocone_base_ker D a c)).comp
        e.symm.toLinearMap
  have hdesc (c : Cocone (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFiniteModuleDiagram (σ := σ) D a)) (r : P₀) :
      desc c (β₀ r) = (c.ι.app 0).hom (Ideal.Quotient.mk (K₀ 0) r) := by
    change Submodule.liftQ (LinearMap.ker b)
      ((c.ι.app 0).hom.comp (Submodule.mkQ (K₀ 0)))
        (by exact _root_.SerrePositivity.BhattScholze.Andre.cocone_base_ker D a c) (e.symm (b r)) = _
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
          (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFiniteEval D a N (Ideal.Quotient.mk (K₀ N) r)) = _
        rw [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFiniteEval_mk, hdesc]
        exact (_root_.SerrePositivity.BhattScholze.Andre.cocone_mk_independent D a c N r).symm
      uniq := by
        intro c f hf
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro z
        obtain ⟨r, rfl⟩ := _root_.SerrePositivity.BhattScholze.deltaDivisionSourceEval_surjective D a₀ z
        have h := congrArg (fun g => g.hom (Ideal.Quotient.mk (K₀ 0) r)) (hf 0)
        change f.hom
          (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFiniteEval D a 0 (Ideal.Quotient.mk (K₀ 0) r)) = _ at h
        rw [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFiniteEval_mk] at h
        exact h.trans (hdesc c r).symm }

/-- 実圏論的colimitと、βで作用する実評価環Aとの標準比較同型。 -/
def Andre.deltaDivisionEvaluationSourceFiniteColimitEvalIso :
    letI := _root_.SerrePositivity.BhattScholze.deltaDivisionSourceEvaluationAlgebra D a₀
    colimit (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFiniteModuleDiagram (σ := σ) D a) ≅
      ModuleCat.of P₀ A := by
  letI := _root_.SerrePositivity.BhattScholze.deltaDivisionSourceEvaluationAlgebra D a₀
  exact (colimit.isColimit _).coconePointUniqueUpToIso
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFiniteEvalIsColimit D a)

/-- 標準colimit比較同型は、各有限商からの標準β評価射を保つ。 -/
theorem Andre.deltaDivisionEvaluationSourceFiniteColimitEvalIso_ι (N : ℕ) :
    letI := _root_.SerrePositivity.BhattScholze.deltaDivisionSourceEvaluationAlgebra D a₀
    colimit.ι (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFiniteModuleDiagram (σ := σ) D a) N ≫
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFiniteColimitEvalIso D a).hom =
        ModuleCat.ofHom (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFiniteEval D a N) := by
  let := _root_.SerrePositivity.BhattScholze.deltaDivisionSourceEvaluationAlgebra D a₀
  exact IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit _)
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFiniteEvalIsColimit D a) N

end SerrePositivity.BhattScholze

end DeltaDivisionSourceEvaluationColimit

/-! ## 余極限との比較交換入力に相対的な任意一元評価環へのTor移送

BSの具体的な有限グラフ商図式だけを扱う。
標準PreservesColimit入力を公開型に保持し、共通余極限との比較のTor消滅補題を再利用する。
-/

@[expose] public noncomputable section DeltaDivisionSourceEvaluationColimitTor

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open _root_.CategoryTheory _root_.CategoryTheory.Limits
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (a : σ → A)
variable {T : Type u} [CommRing T]
local notation "P₀" => RelativeFreeDeltaRing (R := A) σ
local notation "F₀" => _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFiniteModuleDiagram D a

/-- 実有限グラフ商のTor消滅は、明示した余極限との比較交換入力の下で全評価環Aへ移る。 -/
theorem Andre.deltaDivisionEvaluationSource_tor_subsingleton_of_preservesColimit
    (φ : P₀ →+* T) (i : ℕ)
    (hfin : ∀ N : ℕ, Subsingleton (SerrePositivity.TorAlg φ (i + 1)
      (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionEvaluationSourceFiniteQuotient D a N)))
    (hpres : PreservesColimit F₀ ((ModuleCat.extendScalars.{u, u, u} φ).leftDerived (i + 1))) :
    letI := _root_.SerrePositivity.BhattScholze.deltaDivisionSourceEvaluationAlgebra D a
    Subsingleton (SerrePositivity.TorAlg φ (i + 1) A) := by
  let := _root_.SerrePositivity.BhattScholze.deltaDivisionSourceEvaluationAlgebra D a
  have := hpres
  let H := (ModuleCat.extendScalars.{u, u, u} φ).leftDerived (i + 1)
  have hz : IsZero (H.obj (colimit F₀)) :=
    _root_.SerrePositivity.torAlg_colimit_isZero_of_stages φ F₀ (i + 1)
      (fun N => ModuleCat.isZero_iff_subsingleton.mpr (hfin N))
  let e : H.obj (ModuleCat.of P₀ A) ≅ H.obj (colimit F₀) :=
    H.mapIso (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFiniteColimitEvalIso D a).symm
  exact ModuleCat.subsingleton_of_isZero (hz.of_iso e)

end SerrePositivity.BhattScholze

end DeltaDivisionSourceEvaluationColimitTor

/-! ## 任意根族の評価核の有限座標支持による検出 -/

@[expose] public noncomputable section DeltaDivisionEvaluationFiniteSupport

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (a : σ → A)
local notation "L" => RelativeFreeDeltaRing (R := A) σ
local notation "β" => deltaDivisionSourceEval D a

/-- 有限個の実座標グラフ関係で生成される源イデアル。 -/
abbrev Andre.deltaDivisionEvaluationFiniteSupportIdeal (S : Finset (σ × ℕ)) : Ideal L :=
  Ideal.span (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceGraphRelation D a '' (S : Set (σ × ℕ)))

/-- 座標集合の包含は、同じ源環内の関係イデアルの包含を与える。 -/
theorem Andre.deltaDivisionEvaluationFiniteSupportIdeal_mono :
    Monotone (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationFiniteSupportIdeal D a) := by
  intro S T h
  exact Ideal.span_mono (Set.image_mono h)

/-- 任意添字の有限座標イデアルは、有限和集合により有向である。 -/
theorem Andre.deltaDivisionEvaluationFiniteSupportIdeal_directed :
    Directed (· ≤ ·) (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationFiniteSupportIdeal D a) := by
  classical
  intro S T
  exact ⟨S ∪ T, _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationFiniteSupportIdeal_mono D a Finset.subset_union_left,
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationFiniteSupportIdeal_mono D a Finset.subset_union_right⟩

/-- 任意根族の実評価核は、有限座標グラフイデアルの上限。 -/
theorem Andre.deltaDivisionEvaluation_ker_eq_iSup_finiteSupport :
    RingHom.ker β = ⨆ S : Finset (σ × ℕ), _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationFiniteSupportIdeal D a S := by
  classical
  rw [_root_.SerrePositivity.BhattScholze.deltaDivisionSourceEval_ker]
  change Ideal.span (Set.range (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceGraphRelation D a)) = _
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro x ⟨z, rfl⟩
    exact (le_iSup (fun S : Finset (σ × ℕ) =>
      _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationFiniteSupportIdeal D a S) {z})
      (Ideal.subset_span ⟨z, by simp, rfl⟩)
  · apply iSup_le
    intro S
    apply Ideal.span_mono
    rintro x ⟨z, _, rfl⟩
    exact ⟨z, rfl⟩

/-- 元の評価射の等式は、一つの有限座標商での標準像の等式として検出できる。 -/
theorem Andre.deltaDivisionEvaluation_eq_iff_finiteSupport (x y : L) :
    β x = β y ↔ ∃ S : Finset (σ × ℕ),
      Ideal.Quotient.mk (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationFiniteSupportIdeal D a S) x =
        Ideal.Quotient.mk (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationFiniteSupportIdeal D a S) y := by
  have hmem : β x = β y ↔ x - y ∈ RingHom.ker β := by
    change β x = β y ↔ β (x - y) = 0
    rw [map_sub, sub_eq_zero]
  rw [hmem, _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluation_ker_eq_iSup_finiteSupport]
  rw [Submodule.mem_iSup_of_directed _ (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationFiniteSupportIdeal_directed D a)]
  exact exists_congr fun S => (Ideal.Quotient.mk_eq_mk_iff_sub_mem x y).symm

end SerrePositivity.BhattScholze

end DeltaDivisionEvaluationFiniteSupport

/-! ## 任意根族の実評価環は有限座標商の加群余極限 -/

@[expose] public noncomputable section DeltaDivisionEvaluationFiniteSupportColimit

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open _root_.CategoryTheory _root_.CategoryTheory.Limits
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (a : σ → A)
local notation "L" => RelativeFreeDeltaRing (R := A) σ
local notation "β" => deltaDivisionSourceEval D a
local notation "K" => _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationFiniteSupportIdeal D a

/-- 有限座標の包含による、同じ源環の標準商加群射。 -/
def Andre.deltaDivisionFiniteSupportTransition {S T : Finset (σ × ℕ)} (h : S ⊆ T) :
    (L ⧸ K S) →ₗ[L] L ⧸ K T :=
  Submodule.mapQ (K S) (K T) LinearMap.id
    (by exact _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationFiniteSupportIdeal_mono D a h)

/-- 標準遷移射は元の源環の商元を保つ。 -/
theorem Andre.deltaDivisionFiniteSupportTransition_mk {S T : Finset (σ × ℕ)} (h : S ⊆ T)
    (r : L) :
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteSupportTransition D a h (Ideal.Quotient.mk (K S) r) =
      Ideal.Quotient.mk (K T) r := rfl

/-- 任意根族の有限座標商の実加群図式。 -/
def Andre.deltaDivisionFiniteSupportModuleDiagram : Finset (σ × ℕ) ⥤ ModuleCat.{u} L where
  obj S := ModuleCat.of L (L ⧸ K S)
  map h := ModuleCat.ofHom (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteSupportTransition D a (leOfHom h))
  map_id S := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl

private theorem Andre.finiteSupport_le_ker (S : Finset (σ × ℕ)) : K S ≤ RingHom.ker β := by
  rw [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluation_ker_eq_iSup_finiteSupport D a]
  exact le_iSup K S

/-- 各有限座標商から、元のβ作用を持つ評価環への標準線形射。 -/
def Andre.deltaDivisionFiniteSupportEval (S : Finset (σ × ℕ)) :
    letI := _root_.SerrePositivity.BhattScholze.deltaDivisionSourceEvaluationAlgebra D a
    (L ⧸ K S) →ₗ[L] A := by
  letI := _root_.SerrePositivity.BhattScholze.deltaDivisionSourceEvaluationAlgebra D a
  exact Submodule.liftQ (K S) (Algebra.linearMap L A) (by exact _root_.SerrePositivity.BhattScholze.Andre.finiteSupport_le_ker D a S)

/-- 有限座標商の評価射は、元の評価射βの実値を与える。 -/
theorem Andre.deltaDivisionFiniteSupportEval_mk (S : Finset (σ × ℕ)) (r : L) :
    letI := _root_.SerrePositivity.BhattScholze.deltaDivisionSourceEvaluationAlgebra D a
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteSupportEval D a S (Ideal.Quotient.mk (K S) r) = β r := by
  let := _root_.SerrePositivity.BhattScholze.deltaDivisionSourceEvaluationAlgebra D a
  rfl

/-- 元のβ評価環を頂点とする、有限座標商図式の標準余錐。 -/
def Andre.deltaDivisionFiniteSupportEvalCocone :
    letI := _root_.SerrePositivity.BhattScholze.deltaDivisionSourceEvaluationAlgebra D a
    Cocone (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteSupportModuleDiagram D a) := by
  letI := _root_.SerrePositivity.BhattScholze.deltaDivisionSourceEvaluationAlgebra D a
  exact
    { pt := ModuleCat.of L A
      ι :=
        { app := fun S => ModuleCat.ofHom (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteSupportEval D a S)
          naturality := by
            intro S T h
            apply ModuleCat.hom_ext
            apply LinearMap.ext
            intro x
            obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
            rfl } }

/-- 元の評価環は、任意根族の有限座標商図式の実加群余極限である。 -/
def Andre.deltaDivisionFiniteSupportEvalIsColimit :
    letI := _root_.SerrePositivity.BhattScholze.deltaDivisionSourceEvaluationAlgebra D a
    IsColimit (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteSupportEvalCocone D a) := by
  classical
  letI := _root_.SerrePositivity.BhattScholze.deltaDivisionSourceEvaluationAlgebra D a
  let J : σ × ℕ → Ideal L := fun z => Ideal.span {_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceGraphRelation D a z}
  have hK (S : Finset (σ × ℕ)) : K S = S.sup J := by
    induction S using Finset.induction_on with
    | empty => simp [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationFiniteSupportIdeal]
    | @insert z S hz ih =>
      simpa only [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationFiniteSupportIdeal, Finset.coe_insert,
        Set.image_insert_eq, Ideal.span_insert, Finset.sup_insert] using
          congrArg (fun I => J z ⊔ I) ih
  let eF : _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteSupportModuleDiagram D a ≅ _root_.SerrePositivity.finiteSupQuotientDiagram J :=
    NatIso.ofComponents
      (fun S => (Submodule.quotEquivOfEq _ _ (hK S)).toModuleIso) (by
        intro S T h
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro q
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
        rfl)
  let b : L →ₗ[L] A := Algebra.linearMap L A
  have hker : (⨆ z, J z) = LinearMap.ker b := by
    change (⨆ z, J z) = RingHom.ker β
    rw [_root_.SerrePositivity.BhattScholze.deltaDivisionSourceEval_ker, Ideal.span_range_eq_iSup]
    rfl
  let eA := ((Submodule.quotEquivOfEq _ _ hker).trans
    (LinearMap.quotKerEquivOfSurjective b (_root_.SerrePositivity.BhattScholze.deltaDivisionSourceEval_surjective D a))).toModuleIso
  let hc := (IsColimit.precomposeHomEquiv eF (_root_.SerrePositivity.finiteSupQuotientCocone J)).symm
    (_root_.SerrePositivity.finiteSupQuotient_isColimit J)
  refine hc.ofIsoColimit (Cocone.ext eA ?_)
  intro S
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro q
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  rfl

/-- 実圏論的余極限と、元のβ作用を持つ評価環との標準比較同型。 -/
def Andre.deltaDivisionFiniteSupportColimitEvalIso :
    letI := _root_.SerrePositivity.BhattScholze.deltaDivisionSourceEvaluationAlgebra D a
    colimit (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteSupportModuleDiagram D a) ≅ ModuleCat.of L A := by
  letI := _root_.SerrePositivity.BhattScholze.deltaDivisionSourceEvaluationAlgebra D a
  exact (colimit.isColimit _).coconePointUniqueUpToIso
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteSupportEvalIsColimit D a)

/-- 同じ余極限比較は、すべての有限座標商の標準β評価射を保つ。 -/
theorem Andre.deltaDivisionFiniteSupportColimitEvalIso_ι (S : Finset (σ × ℕ)) :
    letI := _root_.SerrePositivity.BhattScholze.deltaDivisionSourceEvaluationAlgebra D a
    colimit.ι (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteSupportModuleDiagram D a) S ≫
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteSupportColimitEvalIso D a).hom =
        ModuleCat.ofHom (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteSupportEval D a S) := by
  let := _root_.SerrePositivity.BhattScholze.deltaDivisionSourceEvaluationAlgebra D a
  exact IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit _)
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteSupportEvalIsColimit D a) S

end SerrePositivity.BhattScholze

end DeltaDivisionEvaluationFiniteSupportColimit

/-! ## 有限部分根族の有界δ深さによる実評価図式 -/

@[expose] public noncomputable section DeltaDivisionBoundedSupportColimit

namespace SerrePositivity.BhattScholze
open _root_.CategoryTheory _root_.CategoryTheory.Limits
variable {σ : Type u}

/-- 有限座標集合を、その根と最大δ深さによる全長方形へ広げる。 -/
def Andre.deltaDivisionCoordinateHull (S : Finset (σ × ℕ)) : Finset (σ × ℕ) := by
  classical
  exact (S.image Prod.fst) ×ˢ Finset.range (S.sup Prod.snd + 1)

/-- 標準長方形は、選ばれた根の最大深さ以下の座標をちょうど含む。 -/
theorem Andre.mem_deltaDivisionCoordinateHull (S : Finset (σ × ℕ)) (z : σ × ℕ) :
    letI : DecidableEq σ := Classical.decEq σ
    z ∈ _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionCoordinateHull S ↔ z.1 ∈ S.image Prod.fst ∧ z.2 ≤ S.sup Prod.snd := by
  classical
  simp only [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionCoordinateHull, Finset.mem_product, Finset.mem_range,
    Nat.lt_succ_iff]

/-- 元のすべての有限座標は、その標準長方形に含まれる。 -/
theorem Andre.subset_deltaDivisionCoordinateHull (S : Finset (σ × ℕ)) :
    S ⊆ _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionCoordinateHull S := by
  classical
  intro z hz
  exact (_root_.SerrePositivity.BhattScholze.Andre.mem_deltaDivisionCoordinateHull S z).mpr
    ⟨Finset.mem_image.mpr ⟨z, hz, rfl⟩, Finset.le_sup hz⟩

/-- 有限座標集合の包含は、標準長方形の包含を与える。 -/
theorem Andre.deltaDivisionCoordinateHull_mono :
    Monotone (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionCoordinateHull (σ := σ)) := by
  classical
  intro S T h z hz
  obtain ⟨hs, hn⟩ := (_root_.SerrePositivity.BhattScholze.Andre.mem_deltaDivisionCoordinateHull S z).mp hz
  exact (_root_.SerrePositivity.BhattScholze.Andre.mem_deltaDivisionCoordinateHull T z).mpr
    ⟨Finset.image_mono Prod.fst h hs, hn.trans (Finset.sup_mono h)⟩

/-- 有限座標添字上の、標準長方形へ広げる関手。 -/
def Andre.deltaDivisionCoordinateHullFunctor : Finset (σ × ℕ) ⥤ Finset (σ × ℕ) :=
  _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionCoordinateHull_mono.functor

/-- この標準長方形関手は余終であり、評価環を尽くす余極限を変えない。 -/
theorem Andre.deltaDivisionCoordinateHullFunctor_final :
    Functor.Final (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionCoordinateHullFunctor (σ := σ)) := by
  classical
  apply Functor.final_of_exists_of_isFiltered
  · intro S
    exact ⟨S, ⟨homOfLE (_root_.SerrePositivity.BhattScholze.Andre.subset_deltaDivisionCoordinateHull S)⟩⟩
  · intro S T f g
    exact ⟨T, 𝟙 T, Subsingleton.elim _ _⟩

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (D : DeltaStructure p A) (a : σ → A)
local notation "L" => RelativeFreeDeltaRing (R := A) σ
local notation "H" => _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionCoordinateHullFunctor (σ := σ)
local notation "F" => _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteSupportModuleDiagram D a

/-- 有限部分根族・全有限δ深さの商のみからなる、元の実図式の前合成。 -/
def Andre.deltaDivisionBoundedSupportModuleDiagram : Finset (σ × ℕ) ⥤ ModuleCat.{u} L := H ⋙ F

/-- 同じβ作用の評価環を頂点に持つ、有界深さ有限部分族の標準余錐。 -/
def Andre.deltaDivisionBoundedSupportEvalCocone :
    letI := _root_.SerrePositivity.BhattScholze.deltaDivisionSourceEvaluationAlgebra D a
    Cocone (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionBoundedSupportModuleDiagram D a) := by
  letI := _root_.SerrePositivity.BhattScholze.deltaDivisionSourceEvaluationAlgebra D a
  exact (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteSupportEvalCocone D a).whisker H

/-- 評価環は、Tor消滅を扱う有界深さ有限部分族の商図式の実余極限である。 -/
def Andre.deltaDivisionBoundedSupportEvalIsColimit :
    letI := _root_.SerrePositivity.BhattScholze.deltaDivisionSourceEvaluationAlgebra D a
    IsColimit (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionBoundedSupportEvalCocone D a) := by
  letI := _root_.SerrePositivity.BhattScholze.deltaDivisionSourceEvaluationAlgebra D a
  letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionCoordinateHullFunctor_final (σ := σ)
  exact (Functor.Final.isColimitWhiskerEquiv H _).symm
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteSupportEvalIsColimit D a)

/-- 有界深さ有限部分族図式の実圏論的余極限と、元のβ評価環との標準同型。 -/
def Andre.deltaDivisionBoundedSupportColimitEvalIso :
    letI := _root_.SerrePositivity.BhattScholze.deltaDivisionSourceEvaluationAlgebra D a
    colimit (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionBoundedSupportModuleDiagram D a) ≅ ModuleCat.of L A := by
  letI := _root_.SerrePositivity.BhattScholze.deltaDivisionSourceEvaluationAlgebra D a
  exact (colimit.isColimit _).coconePointUniqueUpToIso
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionBoundedSupportEvalIsColimit D a)

/-- 標準余極限同型は、全段の元のβ評価射を保つ。 -/
theorem Andre.deltaDivisionBoundedSupportColimitEvalIso_ι (S : Finset (σ × ℕ)) :
    letI := _root_.SerrePositivity.BhattScholze.deltaDivisionSourceEvaluationAlgebra D a
    colimit.ι (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionBoundedSupportModuleDiagram D a) S ≫
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionBoundedSupportColimitEvalIso D a).hom =
        ModuleCat.ofHom (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteSupportEval D a (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionCoordinateHull S)) := by
  let := _root_.SerrePositivity.BhattScholze.deltaDivisionSourceEvaluationAlgebra D a
  exact IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit _)
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionBoundedSupportEvalIsColimit D a) S

end SerrePositivity.BhattScholze

end DeltaDivisionBoundedSupportColimit
