module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFourLastHornConeResidual
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFourLastHornSolution
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGLastHornConePrimitive

/-! # 実四次ホーンの cone 原始元と二未知解

概要：次数 −2 の閉残差の原始元と、Q・A の型付き解を双方向に接続する。
方針：cone 原始元の第一座標の負を Q、第二座標を A として微分式を照合する。
規約：閉性だけから原始元の存在を推論しない。使われ方：追加分母後の高次整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet CochainComplex HomComplex
open scoped _root_.Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]
variable (σ : (Λ[4, 4] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)

/-- 実 cone の原始元の二座標から、元の実ホーンの型付き解を回収する。 -/
def dgFourLastHornSolutionOfConePrimitive (h : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornResidualCone σ).X (-3))
    (dh : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornResidualCone σ).d (-3) (-2) h = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornConeResidual σ) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFourLastHornSolution σ := by
  let φ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornPostcomposition σ
  let u := (mappingCone.fst φ).val.v (-3) (-2) rfl h
  let a := (mappingCone.snd φ).v (-3) (-3) (by decide) h
  have hf : (homObject A D ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 3)).d (-2) (-1) (-u) =
      (mappingCone.fst φ).val.v (-2) (-1) rfl (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornConeResidual σ) :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgComplexConePrimitive_fst φ (-3) h (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornConeResidual σ) dh
  have hs : (homObject A D ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 4)).d (-3) (-2) a =
      (mappingCone.snd φ).v (-2) (-2) (by decide) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornConeResidual σ) +
        φ.f (-2) (-u) := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgComplexConePrimitive_snd φ (-3) h (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornConeResidual σ) dh
  exact ⟨-u, hf.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornConeResidual_fst σ), a,
    hs.trans (congrArg₂ (· + ·) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornConeResidual_snd σ)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornPostcomposition_f σ (-2) (-u)))⟩

/-- 元の実ホーンの型付き解は、残差 cone の次数 −3 の原始元を与える。 -/
def dgFourLastHornConePrimitiveOfSolution (S : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFourLastHornSolution σ) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornResidualCone σ).X (-3) :=
  complexConeElementMk A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornPostcomposition σ) (-3) (-S.Q) S.a

/-- 二未知解から作った cone 成分の微分は、指定された二残差そのもの。 -/
lemma dgFourLastHornConePrimitiveOfSolution_differential (S : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFourLastHornSolution σ) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornResidualCone σ).d (-3) (-2) (dgFourLastHornConePrimitiveOfSolution σ S) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornConeResidual σ := by
  have da : (homObject A D ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 4)).d (-3) (-2) S.a =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornTopResidual σ + (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornPostcomposition σ).f (-2) S.Q :=
    S.differential_a.trans (congrArg (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornTopResidual σ + ·)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornPostcomposition_f σ (-2) S.Q).symm)
  have hg := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgComplexConeElementMk_differential (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornPostcomposition σ) (-3)
  exact hg S.Q S.a (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornMissingResidual σ) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornTopResidual σ)
    S.differential_Q da

/-- 実ホーンの二未知解の存在は、実 cone の指定残差が境界であることと同値。 -/
lemma dgFourLastHornSolution_nonempty_iff_coneResidual_boundary :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFourLastHornSolution σ) ↔
      ∃ h : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornResidualCone σ).X (-3),
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornResidualCone σ).d (-3) (-2) h = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornConeResidual σ := by
  constructor
  · rintro ⟨S⟩
    exact ⟨dgFourLastHornConePrimitiveOfSolution σ S,
      dgFourLastHornConePrimitiveOfSolution_differential σ S⟩
  · rintro ⟨h, dh⟩
    exact ⟨dgFourLastHornSolutionOfConePrimitive σ h dh⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
