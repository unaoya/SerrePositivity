module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGConePrimitiveDegrees
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGLastHornGeneralConeResidual
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGLastHornExpandedSolution

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet CochainComplex HomComplex
open scoped _root_.Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ}
variable (σ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)

/-- 最上位方程式中の最後辺∘Q は、正規化後に同じ後合成鎖写像の像となる。 -/
lemma dgGeneralLastHornPostcomposeQ_normalized
    (Q : GradedHom A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n)) (-(n : ℤ))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport rfl rfl (by omega) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornPostcomposeQ σ Q) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornPostcomposition σ).f (-(n : ℤ)) Q := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornPostcomposeQ
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport_compose (A := A) (D := D) rfl rfl rfl
    (rfl : -(n : ℤ) = -(n : ℤ)) (rfl : (0 : ℤ) = 0)
    (by omega : -(n : ℤ) - 1 + 1 = -(n : ℤ))
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).edgeHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n) (Fin.last (n + 2))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate_lt_last n)) Q (by omega)
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport_refl, LinearEquiv.refl_apply] at hc
  exact hc

/-- 元の実 cone の原始元から、同じ一般ホーンの型付き二未知解を回収する。 -/
def dgGeneralLastHornSolutionOfConePrimitive
    (h : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornResidualCone σ).X (-(n : ℤ) - 1))
    (dh : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornResidualCone σ).d (-(n : ℤ) - 1) (-(n : ℤ)) h =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornConeResidual σ) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGGeneralLastHornSolution σ := by
  let φ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornPostcomposition σ
  let Q := -(mappingCone.fst φ).val.v (-(n : ℤ) - 1) (-(n : ℤ)) (by omega) h
  let a := (mappingCone.snd φ).v (-(n : ℤ) - 1) (-(n : ℤ) - 1) (add_zero _) h
  have hf := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgComplexConePrimitive_fst_at φ (-(n : ℤ) - 1) (-(n : ℤ)) (by omega)
    h (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornConeResidual σ) dh
  have hs := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgComplexConePrimitive_snd_at φ (-(n : ℤ) - 1) (-(n : ℤ)) (by omega)
    h (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornConeResidual σ) dh
  have dQ : differential A Q = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornMissingResidual σ :=
    hf.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornConeResidual_fst σ)
  have da : _root_.SerrePositivity.DifferentialGraded.differential A a =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornTopResidual σ + _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornPostcomposeQ σ Q := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport (A := A) (D := D) (rfl :
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0 = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0) rfl
        (by omega : -(n : ℤ) - 1 + 1 = -(n : ℤ))).injective
    rw [map_add, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedHomTransport_differential_to,
      dgGeneralLastHornPostcomposeQ_normalized]
    exact hs.trans (congrArg (· + φ.f (-(n : ℤ)) Q) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornConeResidual_snd σ))
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornSolutionOfCochains Q dQ a da

/-- 一般二未知解の同じ Q・A を二座標に持つ、次数 −n−1 の cone 成分。 -/
def dgGeneralLastHornConePrimitiveOfSolution (S : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGGeneralLastHornSolution σ) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornResidualCone σ).X (-(n : ℤ) - 1) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgComplexConeElementMkAt (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornPostcomposition σ)
    (-(n : ℤ) - 1) (-(n : ℤ)) (by omega) (-S.Q) S.a

/-- 二未知解から作った cone 成分の微分は、元の指定二残差そのもの。 -/
lemma dgGeneralLastHornConePrimitiveOfSolution_differential (S : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGGeneralLastHornSolution σ) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornResidualCone σ).d (-(n : ℤ) - 1) (-(n : ℤ))
      (dgGeneralLastHornConePrimitiveOfSolution σ S) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornConeResidual σ := by
  have da : (homObject A D ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj (Fin.last (n + 2)))).d
        (-(n : ℤ) - 1) (-(n : ℤ)) S.a = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornNormalizedK σ +
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornPostcomposition σ).f (-(n : ℤ)) S.Q := by
    have hd := congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport (A := A) (D := D) (rfl :
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0 = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0) rfl
        (by omega : -(n : ℤ) - 1 + 1 = -(n : ℤ))) S.differential_a_expanded
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedHomTransport_differential_to, map_add,
      dgGeneralLastHornPostcomposeQ_normalized] at hd
    exact hd
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgComplexConeElementMkAt_differential (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornPostcomposition σ)
    (-(n : ℤ) - 1) (-(n : ℤ)) (by omega) S.Q S.a (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornMissingResidual σ)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornNormalizedK σ) S.differential_Q da

/-- 一般ホーンの二未知解の存在は、指定 cone 残差の境界性と同値。 -/
lemma dgGeneralLastHornSolution_nonempty_iff_coneResidual_boundary :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGGeneralLastHornSolution σ) ↔
      ∃ h : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornResidualCone σ).X (-(n : ℤ) - 1),
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornResidualCone σ).d (-(n : ℤ) - 1) (-(n : ℤ)) h =
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornConeResidual σ := by
  constructor
  · rintro ⟨S⟩
    exact ⟨dgGeneralLastHornConePrimitiveOfSolution σ S,
      dgGeneralLastHornConePrimitiveOfSolution_differential σ S⟩
  · rintro ⟨h, dh⟩
    exact ⟨dgGeneralLastHornSolutionOfConePrimitive σ h dh⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
