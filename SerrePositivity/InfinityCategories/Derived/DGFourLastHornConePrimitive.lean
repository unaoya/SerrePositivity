module
public import SerrePositivity.InfinityCategories.Derived.DGFourLastHornConeResidual
public import SerrePositivity.InfinityCategories.Derived.DGFourLastHornSolution
public import SerrePositivity.InfinityCategories.Derived.DGLastHornConePrimitive

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet CochainComplex HomComplex
open scoped Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]
variable (σ : (Λ[4, 4] : SSet.{max u v}) ⟶ dgNerve A D)

/-- 実 cone の原始元の二座標から、元の実ホーンの型付き解を回収する。 -/
def dgFourLastHornSolutionOfConePrimitive (h : (dgFourLastHornResidualCone σ).X (-3))
    (dh : (dgFourLastHornResidualCone σ).d (-3) (-2) h = dgFourLastHornConeResidual σ) :
    DGFourLastHornSolution σ := by
  let φ := dgFourLastHornPostcomposition σ
  let u := (mappingCone.fst φ).val.v (-3) (-2) rfl h
  let a := (mappingCone.snd φ).v (-3) (-3) (by decide) h
  have hf : (homObject A D ((HornData.knownData σ).obj 0)
      ((HornData.knownData σ).obj 3)).d (-2) (-1) (-u) =
      (mappingCone.fst φ).val.v (-2) (-1) rfl (dgFourLastHornConeResidual σ) :=
    dgComplexConePrimitive_fst φ (-3) h (dgFourLastHornConeResidual σ) dh
  have hs : (homObject A D ((HornData.knownData σ).obj 0)
      ((HornData.knownData σ).obj 4)).d (-3) (-2) a =
      (mappingCone.snd φ).v (-2) (-2) (by decide) (dgFourLastHornConeResidual σ) +
        φ.f (-2) (-u) := dgComplexConePrimitive_snd φ (-3) h (dgFourLastHornConeResidual σ) dh
  exact ⟨-u, hf.trans (dgFourLastHornConeResidual_fst σ), a,
    hs.trans (congrArg₂ (· + ·) (dgFourLastHornConeResidual_snd σ)
      (dgFourLastHornPostcomposition_f σ (-2) (-u)))⟩

/-- 元の実ホーンの型付き解は、残差 cone の次数 −3 の原始元を与える。 -/
def dgFourLastHornConePrimitiveOfSolution (S : DGFourLastHornSolution σ) :
    (dgFourLastHornResidualCone σ).X (-3) :=
  complexConeElementMk A (dgFourLastHornPostcomposition σ) (-3) (-S.Q) S.a

/-- 二未知解から作った cone 成分の微分は、指定された二残差そのもの。 -/
lemma dgFourLastHornConePrimitiveOfSolution_differential (S : DGFourLastHornSolution σ) :
    (dgFourLastHornResidualCone σ).d (-3) (-2) (dgFourLastHornConePrimitiveOfSolution σ S) =
      dgFourLastHornConeResidual σ := by
  have da : (homObject A D ((HornData.knownData σ).obj 0)
      ((HornData.knownData σ).obj 4)).d (-3) (-2) S.a =
      dgFourLastHornTopResidual σ + (dgFourLastHornPostcomposition σ).f (-2) S.Q :=
    S.differential_a.trans (congrArg (dgFourLastHornTopResidual σ + ·)
      (dgFourLastHornPostcomposition_f σ (-2) S.Q).symm)
  have hg := dgComplexConeElementMk_differential (dgFourLastHornPostcomposition σ) (-3)
  exact hg S.Q S.a (dgFourLastHornMissingResidual σ) (dgFourLastHornTopResidual σ)
    S.differential_Q da

/-- 実ホーンの二未知解の存在は、実 cone の指定残差が境界であることと同値。 -/
lemma dgFourLastHornSolution_nonempty_iff_coneResidual_boundary :
    Nonempty (DGFourLastHornSolution σ) ↔
      ∃ h : (dgFourLastHornResidualCone σ).X (-3),
        (dgFourLastHornResidualCone σ).d (-3) (-2) h = dgFourLastHornConeResidual σ := by
  constructor
  · rintro ⟨S⟩
    exact ⟨dgFourLastHornConePrimitiveOfSolution σ S,
      dgFourLastHornConePrimitiveOfSolution_differential σ S⟩
  · rintro ⟨h, dh⟩
    exact ⟨dgFourLastHornSolutionOfConePrimitive σ h dh⟩

end SerrePositivity.InfinityCategories
