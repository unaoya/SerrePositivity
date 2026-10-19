module
public import SerrePositivity.InfinityCategories.Derived.DGCyclePostcomposition
public import SerrePositivity.InfinityCategories.Derived.DGLastHornResidualCompatibility
public import SerrePositivity.InfinityCategories.Derived.DGLastHornFinalEdge
public import SerrePositivity.DifferentialGraded.Complexes.QuasiIsoCycles

/-! # 実最後外ホーンの二残差を Hom 後合成の cone に入れる

概要：実ホーンの R・K を最後の閉辺の後合成鎖写像の cone の次数 −1 の閉成分へ束ねる。
方針：cone の二座標と dR=0・dK=−f23 R を厳密に照合する。
規約：始域は元の回収対象。使われ方：有限分母消去から二未知解を同時に得るための残差。
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
variable (σ : (Λ[3, 3] : SSet.{max u v}) ⟶ dgNerve A D)

/-- 実ホーンの最後の閉辺による、回収始対象からの Hom 後合成鎖写像。 -/
def dgLastHornPostcomposition :=
  dgCyclePostcomposition A D ((HornData.knownData σ).obj 0) (dgLastHornFinalCycle σ)

/-- 実最後閉辺の後合成は、元の通常順斉次合成そのもの。 -/
lemma dgLastHornPostcomposition_f (k : ℤ)
    (f : GradedHom A ((HornData.knownData σ).obj 0) ((HornData.knownData σ).obj 2) k) :
    (dgLastHornPostcomposition σ).f k f =
      compose A ((HornData.knownData σ).edgeHom 2 3 (by decide)) f (add_zero k) := rfl

/-- 二未知残差を入れる、実際の Hom 鎖写像の cone 複体。 -/
def dgLastHornResidualCone : Complex A := mappingCone (dgLastHornPostcomposition σ)

/-- 二残差 R・K を持つ実 cone の次数 −1 の成分。 -/
def dgLastHornConeResidual : (dgLastHornResidualCone σ).X (-1) :=
  complexConeElementMk A (dgLastHornPostcomposition σ) (-1)
    (dgLastHornMissingResidual σ) (dgLastHornTopResidual σ)

/-- cone 残差の第一座標は欠けた三角形の右辺 R。 -/
lemma dgLastHornConeResidual_fst :
    (mappingCone.fst (dgLastHornPostcomposition σ)).val.v (-1) 0 rfl
      (dgLastHornConeResidual σ) = dgLastHornMissingResidual σ :=
  complexConeElementMk_fst A (dgLastHornPostcomposition σ) (-1) _ _

/-- cone 残差の第二座標は最上位方程式の既知部分 K。 -/
lemma dgLastHornConeResidual_snd :
    (mappingCone.snd (dgLastHornPostcomposition σ)).v (-1) (-1) (by decide)
      (dgLastHornConeResidual σ) = dgLastHornTopResidual σ :=
  complexConeElementMk_snd A (dgLastHornPostcomposition σ) (-1) _ _

/-- 元の実ホーンから回収した二残差は、Hom 後合成の cone で実際に閉じている。 -/
lemma dgLastHornConeResidual_closed :
    (dgLastHornResidualCone σ).d (-1) 0 (dgLastHornConeResidual σ) = 0 := by
  apply complexConeElement_ext A (dgLastHornPostcomposition σ) 0
  · have h := complexCone_d_fst A (dgLastHornPostcomposition σ) (-1)
      (dgLastHornConeResidual σ)
    change (mappingCone.fst (dgLastHornPostcomposition σ)).val.v 0 1 rfl
      ((mappingCone (dgLastHornPostcomposition σ)).d (-1) 0 (dgLastHornConeResidual σ)) =
      -(homObject A D ((HornData.knownData σ).obj 0) ((HornData.knownData σ).obj 2)).d 0 1
        ((mappingCone.fst (dgLastHornPostcomposition σ)).val.v (-1) 0 rfl
          (dgLastHornConeResidual σ)) at h
    rw [dgLastHornConeResidual_fst] at h
    have hd : (homObject A D ((HornData.knownData σ).obj 0)
        ((HornData.knownData σ).obj 2)).d 0 1 (dgLastHornMissingResidual σ) = 0 :=
      dgLastHornMissingResidual_closed σ
    rw [hd, neg_zero] at h
    exact h.trans (map_zero _).symm
  · have h := complexCone_d_snd A (dgLastHornPostcomposition σ) (-1)
      (dgLastHornConeResidual σ)
    change (mappingCone.snd (dgLastHornPostcomposition σ)).v 0 0 rfl
      ((mappingCone (dgLastHornPostcomposition σ)).d (-1) 0 (dgLastHornConeResidual σ)) =
      (dgLastHornPostcomposition σ).f 0
        ((mappingCone.fst (dgLastHornPostcomposition σ)).val.v (-1) 0 rfl
          (dgLastHornConeResidual σ)) +
      (homObject A D ((HornData.knownData σ).obj 0) ((HornData.knownData σ).obj 3)).d (-1) 0
        ((mappingCone.snd (dgLastHornPostcomposition σ)).v (-1) (-1) (by decide)
          (dgLastHornConeResidual σ)) at h
    rw [dgLastHornConeResidual_fst, dgLastHornConeResidual_snd] at h
    have he : (dgLastHornPostcomposition σ).f 0 (dgLastHornMissingResidual σ) +
        (homObject A D ((HornData.knownData σ).obj 0) ((HornData.knownData σ).obj 3)).d
          (-1) 0 (dgLastHornTopResidual σ) = 0 := by
      have hk : (homObject A D ((HornData.knownData σ).obj 0)
          ((HornData.knownData σ).obj 3)).d (-1) 0 (dgLastHornTopResidual σ) =
          -compose A ((HornData.knownData σ).edgeHom 2 3 (by decide))
            (dgLastHornMissingResidual σ) (by decide) := dgLastHornTopResidual_differential σ
      exact (congrArg₂ (· + ·)
        (dgLastHornPostcomposition_f σ 0 (dgLastHornMissingResidual σ)) hk).trans
          (add_neg_cancel _)
    exact (h.trans he).trans (map_zero _).symm

end SerrePositivity.InfinityCategories
