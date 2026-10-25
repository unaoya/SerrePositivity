module

public import SerrePositivity.BhattScholze.Delta.Free.RelativeFreePresentation

/-! # δ環でのa_s/dの添加

相対自由δ環へd*x_s=a_sの関係式を課す。BS著者版Notation 2.8、
Proposition 7.2のJ/dのδ添加の代数的部分。d冪ねじれの除去、導来完備化、
反復構成、perfectoid化の存在はこのモジュールには含めない。
-/

@[expose] public noncomputable section
universe u v w
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] {σ : Type v}

/-- 相対自由環でd*x_s=a_sを課す関係式のイデアル。δ安定化前の通常のイデアル。 -/
def deltaDivisionRelationIdeal (d : R) (a : σ → R) :
    Ideal (RelativeFreeDeltaRing (R := R) σ) :=
  Ideal.span (Set.range (fun s : σ ↦
    MvPolynomial.C d * MvPolynomial.X (s, 0) - MvPolynomial.C (a s)))

/-- 基底δ環へa_s/dを添加する環。関係式のδ閉包で相対自由δ環を割る。 -/
abbrev DeltaAdjoinDivision (D : DeltaStructure p R) (d : R) (a : σ → R) :=
  RelativeFreeDeltaRing (R := R) σ ⧸
    (relativeFreeDeltaStructure σ D).deltaClosure (deltaDivisionRelationIdeal d a)

/-- a_s/dの添加環のδ構造。δ安定商の構成をそのまま使う。 -/
def deltaAdjoinDivisionStructure (D : DeltaStructure p R) (d : R) (a : σ → R) :
    DeltaStructure p (DeltaAdjoinDivision D d a) :=
  (relativeFreeDeltaStructure σ D).quotient
    ((relativeFreeDeltaStructure σ D).deltaClosure (deltaDivisionRelationIdeal d a))
    ((relativeFreeDeltaStructure σ D).isStable_deltaClosure (deltaDivisionRelationIdeal d a))

/-- δ添加環への基底の標準射。係数射と商写像を合成する。 -/
def deltaAdjoinDivisionMap (D : DeltaStructure p R) (d : R) (a : σ → R) :
    R →+* DeltaAdjoinDivision D d a :=
  (Ideal.Quotient.mk ((relativeFreeDeltaStructure σ D).deltaClosure
    (deltaDivisionRelationIdeal d a))).comp MvPolynomial.C

/-- δ添加環内のa_s/dを表す初期生成元。 -/
def deltaAdjoinDivisionVariable (D : DeltaStructure p R) (d : R) (a : σ → R)
    (s : σ) : DeltaAdjoinDivision D d a :=
  Ideal.Quotient.mk ((relativeFreeDeltaStructure σ D).deltaClosure
    (deltaDivisionRelationIdeal d a)) (MvPolynomial.X (s, 0))

/-- 基底からa_s/dのδ添加環への標準射はδ射。 -/
theorem deltaAdjoinDivisionMap_isDeltaHom (D : DeltaStructure p R) (d : R) (a : σ → R) :
    D.IsDeltaHom (deltaAdjoinDivisionStructure D d a) (deltaAdjoinDivisionMap D d a) :=
  ((relativeFreeDeltaStructure σ D).isDeltaHom_quotient_mk _
    ((relativeFreeDeltaStructure σ D).isStable_deltaClosure _)).comp
      (relativeFreeDeltaStructure_C_isDeltaHom σ D)

/-- 添加環でd*x_s=a_sが実際に成立する。指定関係式がδ閉包に含まれることを使う。 -/
theorem deltaAdjoinDivision_relation (D : DeltaStructure p R) (d : R) (a : σ → R) (s : σ) :
    deltaAdjoinDivisionMap D d a d * deltaAdjoinDivisionVariable D d a s =
      deltaAdjoinDivisionMap D d a (a s) := by
  let F := relativeFreeDeltaStructure σ D
  let I := deltaDivisionRelationIdeal d a
  let q := Ideal.Quotient.mk (F.deltaClosure I)
  change q (MvPolynomial.C d) * q (MvPolynomial.X (s, 0)) = q (MvPolynomial.C (a s))
  apply sub_eq_zero.mp
  rw [← map_mul, ← map_sub]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply F.le_deltaClosure I
  exact Ideal.subset_span (Set.mem_range_self s)

/-- 基底δ射fと指定した解b_sがf(d)*b_s=f(a_s)を満たせば、
δ添加環からの基底と両立するδ射が一意に存在する。p正則性やdの非零因子性は不要。 -/
theorem existsUnique_deltaAdjoinDivisionHom {A : Type w} [CommRing A]
    (D : DeltaStructure p R) (E : DeltaStructure p A) (d : R) (a : σ → R)
    (f : R →+* A) (hf : D.IsDeltaHom E f) (b : σ → A)
    (hb : ∀ s, f d * b s = f (a s)) :
    ∃! g : DeltaAdjoinDivision D d a →+* A,
      (deltaAdjoinDivisionStructure D d a).IsDeltaHom E g ∧
        g.comp (deltaAdjoinDivisionMap D d a) = f ∧
          ∀ s, g (deltaAdjoinDivisionVariable D d a s) = b s := by
  apply existsUnique_relativeFreePresentationHom D E f hf b (deltaDivisionRelationIdeal d a)
  have hker : deltaDivisionRelationIdeal d a ≤ RingHom.ker (relativeFreeDeltaEval E f b) := by
    apply Ideal.span_le.mpr
    rintro r ⟨s, rfl⟩
    change relativeFreeDeltaEval E f b
      (MvPolynomial.C d * MvPolynomial.X (s, 0) - MvPolynomial.C (a s)) = 0
    rw [map_sub, map_mul, relativeFreeDeltaEval_C, relativeFreeDeltaEval_X,
      relativeFreeDeltaEval_C]
    simpa only [Function.iterate_zero_apply, sub_eq_zero] using hb s
  exact fun r hr ↦ hker hr

end SerrePositivity.BhattScholze
