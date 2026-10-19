module
public import SerrePositivity.InfinityCategories.Derived.DGCyclePostcomposition
public import SerrePositivity.InfinityCategories.Derived.DGFourSimplexResidualCompatibility
public import SerrePositivity.InfinityCategories.Derived.DGFourLastHornFinalEdge
public import SerrePositivity.DifferentialGraded.Complexes.QuasiIsoCycles

/-! # 実四次最後外ホーンの二残差を Hom 後合成の cone に入れる

概要：実ホーンの R・K を最後の閉辺の後合成鎖写像の cone の次数 −2 の閉成分へ束ねる。
方針：cone の二座標と dR=0・dK=−f34 R を厳密に照合する。
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
variable (σ : (Λ[4, 4] : SSet.{max u v}) ⟶ dgNerve A D)

/-- 実ホーンの最後の閉辺による、回収始対象からの Hom 後合成鎖写像。 -/
def dgFourLastHornPostcomposition :=
  dgCyclePostcomposition A D ((HornData.knownData σ).obj 0) (dgFourLastHornFinalCycle σ)

/-- 実四次最後閉辺の後合成は、元の通常順斉次合成そのもの。 -/
lemma dgFourLastHornPostcomposition_f (k : ℤ)
    (f : GradedHom A ((HornData.knownData σ).obj 0) ((HornData.knownData σ).obj 3) k) :
    (dgFourLastHornPostcomposition σ).f k f =
      compose A ((HornData.knownData σ).edgeHom 3 4 (by decide)) f (add_zero k) := rfl

/-- 二未知残差を入れる、実際の Hom 鎖写像の cone 複体。 -/
def dgFourLastHornResidualCone : Complex A := mappingCone (dgFourLastHornPostcomposition σ)

/-- 二残差 R・K を持つ実 cone の次数 −2 の成分。 -/
def dgFourLastHornConeResidual : (dgFourLastHornResidualCone σ).X (-2) :=
  complexConeElementMk A (dgFourLastHornPostcomposition σ) (-2)
    (dgFourLastHornMissingResidual σ) (dgFourLastHornTopResidual σ)

/-- cone 残差の第一座標は欠けた三次面の右辺 R。 -/
lemma dgFourLastHornConeResidual_fst :
    (mappingCone.fst (dgFourLastHornPostcomposition σ)).val.v (-2) (-1) rfl
      (dgFourLastHornConeResidual σ) = dgFourLastHornMissingResidual σ :=
  complexConeElementMk_fst A (dgFourLastHornPostcomposition σ) (-2) _ _

/-- cone 残差の第二座標は最上位方程式の既知部分 K。 -/
lemma dgFourLastHornConeResidual_snd :
    (mappingCone.snd (dgFourLastHornPostcomposition σ)).v (-2) (-2) (by decide)
      (dgFourLastHornConeResidual σ) = dgFourLastHornTopResidual σ :=
  complexConeElementMk_snd A (dgFourLastHornPostcomposition σ) (-2) _ _

/-- 元の実ホーンから回収した二残差は、Hom 後合成の cone で実際に閉じている。 -/
lemma dgFourLastHornConeResidual_closed :
    (dgFourLastHornResidualCone σ).d (-2) (-1) (dgFourLastHornConeResidual σ) = 0 := by
  apply complexConeElement_ext A (dgFourLastHornPostcomposition σ) (-1)
  · have h := complexCone_d_fst A (dgFourLastHornPostcomposition σ) (-2)
      (dgFourLastHornConeResidual σ)
    change (mappingCone.fst (dgFourLastHornPostcomposition σ)).val.v (-1) 0 rfl
      ((mappingCone (dgFourLastHornPostcomposition σ)).d (-2) (-1) (dgFourLastHornConeResidual σ)) =
      -(homObject A D ((HornData.knownData σ).obj 0) ((HornData.knownData σ).obj 3)).d (-1) 0
        ((mappingCone.fst (dgFourLastHornPostcomposition σ)).val.v (-2) (-1) rfl
          (dgFourLastHornConeResidual σ)) at h
    rw [dgFourLastHornConeResidual_fst] at h
    have hd : (homObject A D ((HornData.knownData σ).obj 0)
        ((HornData.knownData σ).obj 3)).d (-1) 0 (dgFourLastHornMissingResidual σ) = 0 :=
      dgFourLastHornMissingResidual_closed σ
    rw [hd, neg_zero] at h
    exact h.trans (map_zero _).symm
  · have h := complexCone_d_snd A (dgFourLastHornPostcomposition σ) (-2)
      (dgFourLastHornConeResidual σ)
    change (mappingCone.snd (dgFourLastHornPostcomposition σ)).v (-1) (-1) rfl
      ((mappingCone (dgFourLastHornPostcomposition σ)).d (-2) (-1) (dgFourLastHornConeResidual σ)) =
      (dgFourLastHornPostcomposition σ).f (-1)
        ((mappingCone.fst (dgFourLastHornPostcomposition σ)).val.v (-2) (-1) rfl
          (dgFourLastHornConeResidual σ)) +
      (homObject A D ((HornData.knownData σ).obj 0) ((HornData.knownData σ).obj 4)).d (-2) (-1)
        ((mappingCone.snd (dgFourLastHornPostcomposition σ)).v (-2) (-2) (by decide)
          (dgFourLastHornConeResidual σ)) at h
    rw [dgFourLastHornConeResidual_fst, dgFourLastHornConeResidual_snd] at h
    have he : (dgFourLastHornPostcomposition σ).f (-1) (dgFourLastHornMissingResidual σ) +
        (homObject A D ((HornData.knownData σ).obj 0) ((HornData.knownData σ).obj 4)).d
          (-2) (-1) (dgFourLastHornTopResidual σ) = 0 := by
      have hk : (homObject A D ((HornData.knownData σ).obj 0)
          ((HornData.knownData σ).obj 4)).d (-2) (-1) (dgFourLastHornTopResidual σ) =
          -compose A ((HornData.knownData σ).edgeHom 3 4 (by decide))
            (dgFourLastHornMissingResidual σ) (by decide) :=
        dgFourLastHornTopResidual_differential σ
      have hp : (dgFourLastHornPostcomposition σ).f (-1) (dgFourLastHornMissingResidual σ) =
          compose A ((HornData.knownData σ).edgeHom 3 4 (by decide))
            (dgFourLastHornMissingResidual σ) (by decide) := by
        exact dgFourLastHornPostcomposition_f σ (-2 + 1) (dgFourLastHornMissingResidual σ)
      exact (congrArg₂ (· + ·) hp hk).trans (add_neg_cancel _)
    exact (h.trans he).trans (map_zero _).symm

end SerrePositivity.InfinityCategories
