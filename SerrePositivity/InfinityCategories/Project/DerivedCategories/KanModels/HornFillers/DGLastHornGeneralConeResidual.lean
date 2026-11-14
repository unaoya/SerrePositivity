module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.HornFillers.DGLastHornGeneralFinalEdge
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.HornFillers.DGLastHornBianchiCompatibility
public import SerrePositivity.DifferentialGraded.Complexes.TensorShift

/-! # 一般最後外ホーンの Hom cone の閉残差

概要：実ホーンの二残差 R・K を、次数 −n の実 Hom cone の閉成分に束ねる。
方針：K の次数だけを線形輸送し、Bianchi の二微分式を cone の二座標へ渡す。
規約：原始元の存在は要求しない。使われ方：有限分母消去による一般次数の充填。
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

/-- K を同じ始終対象の次数 −n に正規化する線形輸送。 -/
def dgGeneralLastHornNormalizedK : GradedHom A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj (Fin.last (n + 2))) (-(n : ℤ)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport rfl rfl (by omega) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornTopResidual σ)

/-- 正規化した K の微分は、同じ最後辺による R の後合成の負。 -/
lemma dgGeneralLastHornNormalizedK_differential :
    _root_.SerrePositivity.DifferentialGraded.differential A (dgGeneralLastHornNormalizedK σ) =
      -(_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornPostcomposition σ).f (-(n : ℤ) + 1)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornMissingResidual σ) := by
  unfold dgGeneralLastHornNormalizedK
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport_differential, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornTopResidual_differential, map_neg]
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornPostcomposeR
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport_compose (A := A) (D := D) rfl rfl rfl
    (rfl : -(n : ℤ) + 1 = -(n : ℤ) + 1) (rfl : (0 : ℤ) = 0)
    (by omega : -(n : ℤ) - 1 + 1 + 1 = -(n : ℤ) + 1)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).edgeHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n) (Fin.last (n + 2))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate_lt_last n)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornMissingResidual σ) (by omega)
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport_refl, LinearEquiv.refl_apply] at hc
  exact congrArg Neg.neg hc

/-- 最後の閉辺の Hom 後合成鎖写像の実 cone。 -/
def dgGeneralLastHornResidualCone : Complex A := mappingCone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornPostcomposition σ)

/-- 二残差をそのまま二座標に持つ、次数 −n の実 cone 成分。 -/
def dgGeneralLastHornConeResidual : (dgGeneralLastHornResidualCone σ).X (-(n : ℤ)) :=
  complexConeElementMk A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornPostcomposition σ) (-(n : ℤ))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornMissingResidual σ) (dgGeneralLastHornNormalizedK σ)

/-- 実 cone 残差の第一座標は欠面右辺 R。 -/
lemma dgGeneralLastHornConeResidual_fst :
    (mappingCone.fst (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornPostcomposition σ)).val.v (-(n : ℤ)) (-(n : ℤ) + 1) rfl
      (dgGeneralLastHornConeResidual σ) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornMissingResidual σ :=
  complexConeElementMk_fst A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornPostcomposition σ) (-(n : ℤ)) _ _

/-- 実 cone 残差の第二座標は同じ端点・標準次数の K。 -/
lemma dgGeneralLastHornConeResidual_snd :
    (mappingCone.snd (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornPostcomposition σ)).v (-(n : ℤ)) (-(n : ℤ)) (add_zero _)
      (dgGeneralLastHornConeResidual σ) = dgGeneralLastHornNormalizedK σ :=
  complexConeElementMk_snd A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornPostcomposition σ) (-(n : ℤ)) _ _

/-- 元の実ホーンから回収した二残差は、全次元で実 Hom cone 内の閉成分になる。 -/
lemma dgGeneralLastHornConeResidual_closed :
    (dgGeneralLastHornResidualCone σ).d (-(n : ℤ)) (-(n : ℤ) + 1)
      (dgGeneralLastHornConeResidual σ) = 0 := by
  apply complexConeElement_ext A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornPostcomposition σ) (-(n : ℤ) + 1)
  · have h := complexCone_d_fst A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornPostcomposition σ) (-(n : ℤ))
      (dgGeneralLastHornConeResidual σ)
    rw [dgGeneralLastHornConeResidual_fst] at h
    have hd : (homObject A D ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n))).d
          (-(n : ℤ) + 1) (-(n : ℤ) + 1 + 1) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornMissingResidual σ) = 0 :=
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornMissingResidual_closed σ
    rw [hd, neg_zero] at h
    exact h.trans (map_zero _).symm
  · have h := complexCone_d_snd A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornPostcomposition σ) (-(n : ℤ))
      (dgGeneralLastHornConeResidual σ)
    rw [dgGeneralLastHornConeResidual_fst, dgGeneralLastHornConeResidual_snd] at h
    have hd : (homObject A D ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj (Fin.last (n + 2)))).d
          (-(n : ℤ)) (-(n : ℤ) + 1) (dgGeneralLastHornNormalizedK σ) =
        -(_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornPostcomposition σ).f (-(n : ℤ) + 1)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornMissingResidual σ) := dgGeneralLastHornNormalizedK_differential σ
    rw [hd, add_neg_cancel] at h
    exact h.trans (map_zero _).symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories
