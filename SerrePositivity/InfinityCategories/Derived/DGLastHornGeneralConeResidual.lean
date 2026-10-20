module
public import SerrePositivity.InfinityCategories.Derived.DGLastHornGeneralFinalEdge
public import SerrePositivity.InfinityCategories.Derived.DGLastHornBianchiCompatibility
public import SerrePositivity.DifferentialGraded.Complexes.QuasiIsoCycles

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet CochainComplex HomComplex
open scoped Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] {n : ℕ}
variable (σ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{max u v}) ⟶ dgNerve A D)

/-- K を同じ始終対象の次数 −n に正規化する線形輸送。 -/
def dgGeneralLastHornNormalizedK : GradedHom A ((HornData.knownData σ).obj 0)
    ((HornData.knownData σ).obj (Fin.last (n + 2))) (-(n : ℤ)) :=
  gradedHomTransport rfl rfl (by omega) (dgGeneralLastHornTopResidual σ)

/-- 正規化した K の微分は、同じ最後辺による R の後合成の負。 -/
lemma dgGeneralLastHornNormalizedK_differential :
    differential A (dgGeneralLastHornNormalizedK σ) =
      -(dgGeneralLastHornPostcomposition σ).f (-(n : ℤ) + 1)
        (dgGeneralLastHornMissingResidual σ) := by
  unfold dgGeneralLastHornNormalizedK
  rw [← gradedHomTransport_differential, dgGeneralLastHornTopResidual_differential, map_neg]
  unfold dgGeneralLastHornPostcomposeR
  have hc := gradedHomTransport_compose (A := A) (D := D) rfl rfl rfl
    (rfl : -(n : ℤ) + 1 = -(n : ℤ) + 1) (rfl : (0 : ℤ) = 0)
    (by omega : -(n : ℤ) - 1 + 1 + 1 = -(n : ℤ) + 1)
    ((HornData.knownData σ).edgeHom (dgLastHornPenultimate n) (Fin.last (n + 2))
      (dgLastHornPenultimate_lt_last n)) (dgGeneralLastHornMissingResidual σ) (by omega)
  simp only [gradedHomTransport_refl, LinearEquiv.refl_apply] at hc
  exact congrArg Neg.neg hc

/-- 最後の閉辺の Hom 後合成鎖写像の実 cone。 -/
def dgGeneralLastHornResidualCone : Complex A := mappingCone (dgGeneralLastHornPostcomposition σ)

/-- 二残差をそのまま二座標に持つ、次数 −n の実 cone 成分。 -/
def dgGeneralLastHornConeResidual : (dgGeneralLastHornResidualCone σ).X (-(n : ℤ)) :=
  complexConeElementMk A (dgGeneralLastHornPostcomposition σ) (-(n : ℤ))
    (dgGeneralLastHornMissingResidual σ) (dgGeneralLastHornNormalizedK σ)

/-- 実 cone 残差の第一座標は欠面右辺 R。 -/
lemma dgGeneralLastHornConeResidual_fst :
    (mappingCone.fst (dgGeneralLastHornPostcomposition σ)).val.v (-(n : ℤ)) (-(n : ℤ) + 1) rfl
      (dgGeneralLastHornConeResidual σ) = dgGeneralLastHornMissingResidual σ :=
  complexConeElementMk_fst A (dgGeneralLastHornPostcomposition σ) (-(n : ℤ)) _ _

/-- 実 cone 残差の第二座標は同じ端点・標準次数の K。 -/
lemma dgGeneralLastHornConeResidual_snd :
    (mappingCone.snd (dgGeneralLastHornPostcomposition σ)).v (-(n : ℤ)) (-(n : ℤ)) (add_zero _)
      (dgGeneralLastHornConeResidual σ) = dgGeneralLastHornNormalizedK σ :=
  complexConeElementMk_snd A (dgGeneralLastHornPostcomposition σ) (-(n : ℤ)) _ _

/-- 元の実ホーンから回収した二残差は、全次元で実 Hom cone 内の閉成分になる。 -/
lemma dgGeneralLastHornConeResidual_closed :
    (dgGeneralLastHornResidualCone σ).d (-(n : ℤ)) (-(n : ℤ) + 1)
      (dgGeneralLastHornConeResidual σ) = 0 := by
  apply complexConeElement_ext A (dgGeneralLastHornPostcomposition σ) (-(n : ℤ) + 1)
  · have h := complexCone_d_fst A (dgGeneralLastHornPostcomposition σ) (-(n : ℤ))
      (dgGeneralLastHornConeResidual σ)
    rw [dgGeneralLastHornConeResidual_fst] at h
    have hd : (homObject A D ((HornData.knownData σ).obj 0)
        ((HornData.knownData σ).obj (dgLastHornPenultimate n))).d
          (-(n : ℤ) + 1) (-(n : ℤ) + 1 + 1) (dgGeneralLastHornMissingResidual σ) = 0 :=
      dgGeneralLastHornMissingResidual_closed σ
    rw [hd, neg_zero] at h
    exact h.trans (map_zero _).symm
  · have h := complexCone_d_snd A (dgGeneralLastHornPostcomposition σ) (-(n : ℤ))
      (dgGeneralLastHornConeResidual σ)
    rw [dgGeneralLastHornConeResidual_fst, dgGeneralLastHornConeResidual_snd] at h
    have hd : (homObject A D ((HornData.knownData σ).obj 0)
        ((HornData.knownData σ).obj (Fin.last (n + 2)))).d
          (-(n : ℤ)) (-(n : ℤ) + 1) (dgGeneralLastHornNormalizedK σ) =
        -(dgGeneralLastHornPostcomposition σ).f (-(n : ℤ) + 1)
          (dgGeneralLastHornMissingResidual σ) := dgGeneralLastHornNormalizedK_differential σ
    rw [hd, add_neg_cancel] at h
    exact h.trans (map_zero _).symm

end SerrePositivity.InfinityCategories
