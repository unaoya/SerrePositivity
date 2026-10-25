module

public import SerrePositivity.BhattScholze.Delta.Division.Relations.DeltaDivisionFiniteEvaluationRelations

/-! # 自由δ射の評価源とraw δ包の核表示

源P=A{x_s}からx_s↦d z_sとx_s↦a_sの二つの実δ射を置く。
座標グラフ核の像が、既存raw δ除算包の実定義イデアルとなることを証明する。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 源自由δ環から、初期変数x_sをd z_sへ送る実δ射の underlying 環射。 -/
def deltaDivisionSourceMap (D : DeltaStructure p A) (d : A) :
    RelativeFreeDeltaRing (R := A) σ →+* RelativeFreeDeltaRing (R := A) σ :=
  relativeFreeDeltaEval (relativeFreeDeltaStructure σ D) MvPolynomial.C
    (fun s => MvPolynomial.C d * MvPolynomial.X (s, 0))

/-- 源自由δ環からa_sへ評価する実環射。 -/
def deltaDivisionSourceEval (D : DeltaStructure p A) (a : σ → A) :
    RelativeFreeDeltaRing (R := A) σ →+* A :=
  relativeFreeDeltaEval D (RingHom.id A) a

/-- d z_sへの自由評価射は既存δ構造を保存する。 -/
theorem deltaDivisionSourceMap_isDeltaHom (D : DeltaStructure p A) (d : A) :
    (relativeFreeDeltaStructure σ D).IsDeltaHom (relativeFreeDeltaStructure σ D)
      (deltaDivisionSourceMap D d) :=
  relativeFreeDeltaEval_isDeltaHom D _ _ (relativeFreeDeltaStructure_C_isDeltaHom σ D) _

/-- a_sへの自由評価射も既存δ構造を保存する。 -/
theorem deltaDivisionSourceEval_isDeltaHom (D : DeltaStructure p A) (a : σ → A) :
    (relativeFreeDeltaStructure σ D).IsDeltaHom D (deltaDivisionSourceEval D a) :=
  relativeFreeDeltaEval_isDeltaHom D D _ (fun _ => rfl) a

/-- 源自由δ射は元の係数を固定する。 -/
theorem deltaDivisionSourceMap_C (D : DeltaStructure p A) (d r : A) :
    deltaDivisionSourceMap (σ := σ) D d (MvPolynomial.C r) = MvPolynomial.C r :=
  relativeFreeDeltaEval_C _ _ _ _

/-- 源評価射も元の係数上では恒等写像。 -/
theorem deltaDivisionSourceEval_C (D : DeltaStructure p A) (a : σ → A) (r : A) :
    deltaDivisionSourceEval D a (MvPolynomial.C r) = r :=
  relativeFreeDeltaEval_C _ _ _ _

/-- 全δ座標の像はd z_sの実反復δ像。 -/
theorem deltaDivisionSourceMap_X (D : DeltaStructure p A) (d : A) (s : σ) (n : ℕ) :
    deltaDivisionSourceMap D d (MvPolynomial.X (s, n)) =
      (relativeFreeDeltaStructure σ D).delta^[n] (MvPolynomial.C d * MvPolynomial.X (s, 0)) :=
  relativeFreeDeltaEval_X _ _ _ _ _

/-- 全δ座標の評価はa_sの実反復δ像。 -/
theorem deltaDivisionSourceEval_X (D : DeltaStructure p A) (a : σ → A) (s : σ) (n : ℕ) :
    deltaDivisionSourceEval D a (MvPolynomial.X (s, n)) = D.delta^[n] (a s) :=
  relativeFreeDeltaEval_X _ _ _ _ _

/-- 源評価射の核は、全座標グラフ関係で生成される。 -/
theorem deltaDivisionSourceEval_ker (D : DeltaStructure p A) (a : σ → A) :
    RingHom.ker (deltaDivisionSourceEval D a) =
      Ideal.span (Set.range fun z : σ × ℕ =>
        MvPolynomial.X z - MvPolynomial.C (D.delta^[z.2] (a z.1))) := by
  let K : Ideal (RelativeFreeDeltaRing (R := A) σ) :=
    Ideal.span (Set.range fun z : σ × ℕ =>
      MvPolynomial.X z - MvPolynomial.C (D.delta^[z.2] (a z.1)))
  have hK : K ≤ RingHom.ker (deltaDivisionSourceEval D a) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨⟨s, n⟩, rfl⟩
    change deltaDivisionSourceEval D a
      (MvPolynomial.X (s, n) - MvPolynomial.C (D.delta^[n] (a s))) = 0
    rw [map_sub, deltaDivisionSourceEval_X, deltaDivisionSourceEval_C, sub_self]
  let q := Ideal.Quotient.mk K
  have hq : q = (q.comp MvPolynomial.C).comp (deltaDivisionSourceEval D a) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      rw [RingHom.comp_apply, RingHom.comp_apply, deltaDivisionSourceEval_C]
    · rintro ⟨s, n⟩
      rw [RingHom.comp_apply, RingHom.comp_apply, deltaDivisionSourceEval_X]
      apply sub_eq_zero.mp
      rw [← map_sub]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨(s, n), rfl⟩)
  apply le_antisymm ?_ hK
  intro f hf
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change q f = 0
  rw [hq]
  change q (MvPolynomial.C (deltaDivisionSourceEval D a f)) = 0
  rw [show deltaDivisionSourceEval D a f = 0 from hf, map_zero, map_zero]

/-- 核の座標グラフ関係の像は、前工程の実評価関係そのもの。 -/
theorem deltaDivisionSourceMap_graphRelation (D : DeltaStructure p A) (d : A) (a : σ → A)
    (s : σ) (n : ℕ) :
    deltaDivisionSourceMap D d
      (MvPolynomial.X (s, n) - MvPolynomial.C (D.delta^[n] (a s))) =
      deltaDivisionEvaluationRelation D d a s n := by
  rw [map_sub, deltaDivisionSourceMap_X, deltaDivisionSourceMap_C,
    deltaDivisionEvaluationRelation_eq]

/-- 源評価射の核の像イデアルは、実raw δ除算包の定義δ閉包。 -/
theorem deltaDivisionSourceMap_eval_ker (D : DeltaStructure p A) (d : A) (a : σ → A) :
    (RingHom.ker (deltaDivisionSourceEval D a)).map (deltaDivisionSourceMap D d) =
      (relativeFreeDeltaStructure σ D).deltaClosure (deltaDivisionRelationIdeal d a) := by
  rw [deltaDivisionSourceEval_ker, Ideal.map_span, ← Set.range_comp']
  change Ideal.span (Set.range fun z : σ × ℕ => deltaDivisionSourceMap D d
    (MvPolynomial.X z - MvPolynomial.C (D.delta^[z.2] (a z.1)))) = _
  have hg : (fun z : σ × ℕ => deltaDivisionSourceMap D d
      (MvPolynomial.X z - MvPolynomial.C (D.delta^[z.2] (a z.1)))) =
      (fun z : σ × ℕ => deltaDivisionEvaluationRelation D d a z.1 z.2) :=
    funext (fun z => deltaDivisionSourceMap_graphRelation D d a z.1 z.2)
  rw [hg]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨⟨s, n⟩, rfl⟩
    exact Ideal.Quotient.eq_zero_iff_mem.mp
      (deltaDivisionEvaluationRelation_quotient_eq_zero D d a s n)
  · rw [deltaDivision_deltaClosure_eq_iSup_finiteRelations]
    apply iSup_le
    intro N
    rw [← deltaDivisionFiniteEvaluationIdeal_eq]
    apply Ideal.span_le.mpr
    rintro _ ⟨⟨s, i⟩, rfl⟩
    exact Ideal.subset_span ⟨(s, i.val), rfl⟩

/-- 実raw商射と基底射は、源自由δ射と源評価射の四角を可換にする。 -/
theorem deltaDivisionSource_raw_square (D : DeltaStructure p A) (d : A) (a : σ → A) :
    (Ideal.Quotient.mk ((relativeFreeDeltaStructure σ D).deltaClosure
      (deltaDivisionRelationIdeal d a))).comp (deltaDivisionSourceMap D d) =
        (deltaAdjoinDivisionMap D d a).comp (deltaDivisionSourceEval D a) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, deltaDivisionSourceMap_C, deltaDivisionSourceEval_C]
    rfl
  · rintro ⟨s, n⟩
    simp only [RingHom.comp_apply, deltaDivisionSourceMap_X, deltaDivisionSourceEval_X]
    apply sub_eq_zero.mp
    change Ideal.Quotient.mk _
      ((relativeFreeDeltaStructure σ D).delta^[n] (MvPolynomial.C d * MvPolynomial.X (s, 0))) -
        Ideal.Quotient.mk _ (MvPolynomial.C (D.delta^[n] (a s))) = 0
    rw [← map_sub, ← deltaDivisionEvaluationRelation_eq]
    exact deltaDivisionEvaluationRelation_quotient_eq_zero D d a s n

/-- raw δ包は、具体的な自由δ射と評価射の通常の可換環pushoutを与える。
終域のδ構造や完備性を仮定しない。導来pushoutの主張とは区別する。 -/
theorem existsUnique_deltaDivisionSourceRawLift {B : Type*} [CommRing B]
    (D : DeltaStructure p A) (d : A) (a : σ → A)
    (f : A →+* B) (g : RelativeFreeDeltaRing (R := A) σ →+* B)
    (h : g.comp (deltaDivisionSourceMap D d) = f.comp (deltaDivisionSourceEval D a)) :
    ∃! k : DeltaAdjoinDivision D d a →+* B,
      k.comp (Ideal.Quotient.mk ((relativeFreeDeltaStructure σ D).deltaClosure
        (deltaDivisionRelationIdeal d a))) = g ∧
      k.comp (deltaAdjoinDivisionMap D d a) = f := by
  let J := (relativeFreeDeltaStructure σ D).deltaClosure (deltaDivisionRelationIdeal d a)
  have hJ : J ≤ RingHom.ker g := by
    change (relativeFreeDeltaStructure σ D).deltaClosure (deltaDivisionRelationIdeal d a) ≤ _
    rw [← deltaDivisionSourceMap_eval_ker]
    apply Ideal.map_le_iff_le_comap.mpr
    intro r hr
    change g (deltaDivisionSourceMap D d r) = 0
    have he := RingHom.congr_fun h r
    change g (deltaDivisionSourceMap D d r) = f (deltaDivisionSourceEval D a r) at he
    rw [he, show deltaDivisionSourceEval D a r = 0 from hr, map_zero]
  let k := Ideal.Quotient.lift J g hJ
  have hk : k.comp (Ideal.Quotient.mk J) = g := by
    apply RingHom.ext
    intro r
    exact Ideal.Quotient.lift_mk J g hJ
  refine ⟨k, ⟨hk, ?_⟩, ?_⟩
  · apply RingHom.ext
    intro r
    change k (Ideal.Quotient.mk J (MvPolynomial.C r)) = f r
    rw [Ideal.Quotient.lift_mk]
    have he := RingHom.congr_fun h (MvPolynomial.C r)
    simpa only [RingHom.comp_apply, deltaDivisionSourceMap_C, deltaDivisionSourceEval_C] using he
  · intro l hl
    apply Ideal.Quotient.ringHom_ext
    exact hl.1.trans hk.symm

end SerrePositivity.BhattScholze
