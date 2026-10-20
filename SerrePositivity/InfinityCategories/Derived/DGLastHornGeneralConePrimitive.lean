module
public import SerrePositivity.InfinityCategories.Derived.DGConePrimitiveDegrees
public import SerrePositivity.InfinityCategories.Derived.DGLastHornGeneralConeResidual
public import SerrePositivity.InfinityCategories.Derived.DGLastHornExpandedSolution

/-! # 一般最後外ホーンの cone 原始元と二未知解

概要：実 Hom cone の原始元から Q・A を回収し、一般の指定ホーンを充填する。
方針：第一座標の負を Q、第二座標を A とし、K の次数輸送の単射性で照合する。
規約：存在は指定残差の境界性と同値。使われ方：分母後の原始元から実充填への接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet CochainComplex HomComplex
open scoped Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] {n : ℕ}
variable (σ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{max u v}) ⟶ dgNerve A D)

/-- 最上位方程式中の最後辺∘Q は、正規化後に同じ後合成鎖写像の像となる。 -/
lemma dgGeneralLastHornPostcomposeQ_normalized
    (Q : GradedHom A ((HornData.knownData σ).obj 0)
      ((HornData.knownData σ).obj (dgLastHornPenultimate n)) (-(n : ℤ))) :
    gradedHomTransport rfl rfl (by omega) (dgGeneralLastHornPostcomposeQ σ Q) =
      (dgGeneralLastHornPostcomposition σ).f (-(n : ℤ)) Q := by
  unfold dgGeneralLastHornPostcomposeQ
  have hc := gradedHomTransport_compose (A := A) (D := D) rfl rfl rfl
    (rfl : -(n : ℤ) = -(n : ℤ)) (rfl : (0 : ℤ) = 0)
    (by omega : -(n : ℤ) - 1 + 1 = -(n : ℤ))
    ((HornData.knownData σ).edgeHom (dgLastHornPenultimate n) (Fin.last (n + 2))
      (dgLastHornPenultimate_lt_last n)) Q (by omega)
  simp only [gradedHomTransport_refl, LinearEquiv.refl_apply] at hc
  exact hc

/-- 元の実 cone の原始元から、同じ一般ホーンの型付き二未知解を回収する。 -/
def dgGeneralLastHornSolutionOfConePrimitive
    (h : (dgGeneralLastHornResidualCone σ).X (-(n : ℤ) - 1))
    (dh : (dgGeneralLastHornResidualCone σ).d (-(n : ℤ) - 1) (-(n : ℤ)) h =
      dgGeneralLastHornConeResidual σ) : DGGeneralLastHornSolution σ := by
  let φ := dgGeneralLastHornPostcomposition σ
  let Q := -(mappingCone.fst φ).val.v (-(n : ℤ) - 1) (-(n : ℤ)) (by omega) h
  let a := (mappingCone.snd φ).v (-(n : ℤ) - 1) (-(n : ℤ) - 1) (add_zero _) h
  have hf := dgComplexConePrimitive_fst_at φ (-(n : ℤ) - 1) (-(n : ℤ)) (by omega)
    h (dgGeneralLastHornConeResidual σ) dh
  have hs := dgComplexConePrimitive_snd_at φ (-(n : ℤ) - 1) (-(n : ℤ)) (by omega)
    h (dgGeneralLastHornConeResidual σ) dh
  have dQ : differential A Q = dgGeneralLastHornMissingResidual σ :=
    hf.trans (dgGeneralLastHornConeResidual_fst σ)
  have da : differential A a =
      dgGeneralLastHornTopResidual σ + dgGeneralLastHornPostcomposeQ σ Q := by
    apply (gradedHomTransport (A := A) (D := D) (rfl :
      (HornData.knownData σ).obj 0 = (HornData.knownData σ).obj 0) rfl
        (by omega : -(n : ℤ) - 1 + 1 = -(n : ℤ))).injective
    rw [map_add, dgGradedHomTransport_differential_to,
      dgGeneralLastHornPostcomposeQ_normalized]
    exact hs.trans (congrArg (· + φ.f (-(n : ℤ)) Q) (dgGeneralLastHornConeResidual_snd σ))
  exact dgGeneralLastHornSolutionOfCochains Q dQ a da

/-- 一般二未知解の同じ Q・A を二座標に持つ、次数 −n−1 の cone 成分。 -/
def dgGeneralLastHornConePrimitiveOfSolution (S : DGGeneralLastHornSolution σ) :
    (dgGeneralLastHornResidualCone σ).X (-(n : ℤ) - 1) :=
  dgComplexConeElementMkAt (dgGeneralLastHornPostcomposition σ)
    (-(n : ℤ) - 1) (-(n : ℤ)) (by omega) (-S.Q) S.a

/-- 二未知解から作った cone 成分の微分は、元の指定二残差そのもの。 -/
lemma dgGeneralLastHornConePrimitiveOfSolution_differential (S : DGGeneralLastHornSolution σ) :
    (dgGeneralLastHornResidualCone σ).d (-(n : ℤ) - 1) (-(n : ℤ))
      (dgGeneralLastHornConePrimitiveOfSolution σ S) = dgGeneralLastHornConeResidual σ := by
  have da : (homObject A D ((HornData.knownData σ).obj 0)
      ((HornData.knownData σ).obj (Fin.last (n + 2)))).d
        (-(n : ℤ) - 1) (-(n : ℤ)) S.a = dgGeneralLastHornNormalizedK σ +
          (dgGeneralLastHornPostcomposition σ).f (-(n : ℤ)) S.Q := by
    have hd := congrArg (gradedHomTransport (A := A) (D := D) (rfl :
      (HornData.knownData σ).obj 0 = (HornData.knownData σ).obj 0) rfl
        (by omega : -(n : ℤ) - 1 + 1 = -(n : ℤ))) S.differential_a_expanded
    rw [dgGradedHomTransport_differential_to, map_add,
      dgGeneralLastHornPostcomposeQ_normalized] at hd
    exact hd
  exact dgComplexConeElementMkAt_differential (dgGeneralLastHornPostcomposition σ)
    (-(n : ℤ) - 1) (-(n : ℤ)) (by omega) S.Q S.a (dgGeneralLastHornMissingResidual σ)
    (dgGeneralLastHornNormalizedK σ) S.differential_Q da

/-- 一般ホーンの二未知解の存在は、指定 cone 残差の境界性と同値。 -/
lemma dgGeneralLastHornSolution_nonempty_iff_coneResidual_boundary :
    Nonempty (DGGeneralLastHornSolution σ) ↔
      ∃ h : (dgGeneralLastHornResidualCone σ).X (-(n : ℤ) - 1),
        (dgGeneralLastHornResidualCone σ).d (-(n : ℤ) - 1) (-(n : ℤ)) h =
          dgGeneralLastHornConeResidual σ := by
  constructor
  · rintro ⟨S⟩
    exact ⟨dgGeneralLastHornConePrimitiveOfSolution σ S,
      dgGeneralLastHornConePrimitiveOfSolution_differential σ S⟩
  · rintro ⟨h, dh⟩
    exact ⟨dgGeneralLastHornSolutionOfConePrimitive σ h dh⟩

end SerrePositivity.InfinityCategories
