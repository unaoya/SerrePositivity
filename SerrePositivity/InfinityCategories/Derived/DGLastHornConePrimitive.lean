module
public import SerrePositivity.InfinityCategories.Derived.DGLastHornConeResidual
public import SerrePositivity.InfinityCategories.Derived.DGLastHornSolution

/-! # 実最後外ホーンの cone 原始元と二未知解

概要：残差 cone の原始元と、元の指定三面を保つ Q・A の解を双方向に接続する。
方針：cone の第一座標の負を Q、第二座標を A とし、二つの微分式を照合する。
規約：閉性だけから原始元の存在を推論しない。使われ方：追加分母細分後の解の回収。
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
/-- cone 原始元の第一座標の負は、残差の第一座標の原始元。 -/
lemma dgComplexConePrimitive_fst {M N : Complex A} (f : M ⟶ N) (q : ℤ)
    (h : (mappingCone f).X q) (z : (mappingCone f).X (q + 1))
    (dh : (mappingCone f).d q (q + 1) h = z) :
    M.d (q + 1) (q + 1 + 1) (-(mappingCone.fst f).val.v q (q + 1) rfl h) =
      (mappingCone.fst f).val.v (q + 1) (q + 1 + 1) rfl z := by
  have hf := complexCone_d_fst A f q h
  rw [dh] at hf
  exact (map_neg _ _).trans hf.symm

/-- cone 原始元の第二座標の微分は、残差と負の第一座標の像との和。 -/
lemma dgComplexConePrimitive_snd {M N : Complex A} (f : M ⟶ N) (q : ℤ)
    (h : (mappingCone f).X q) (z : (mappingCone f).X (q + 1))
    (dh : (mappingCone f).d q (q + 1) h = z) :
    N.d q (q + 1) ((mappingCone.snd f).v q q (add_zero q) h) =
      (mappingCone.snd f).v (q + 1) (q + 1) (add_zero _) z +
        f.f (q + 1) (-(mappingCone.fst f).val.v q (q + 1) rfl h) := by
  have hs := complexCone_d_snd A f q h
  rw [dh] at hs
  rw [map_neg]
  simpa only [sub_eq_add_neg] using eq_sub_of_add_eq ((add_comm _ _).trans hs.symm)

/-- 二つの座標微分式から、cone の指定原始元の微分を照合する。 -/
lemma dgComplexConeElementMk_differential {M N : Complex A} (f : M ⟶ N) (q : ℤ)
    (u : M.X (q + 1)) (v : N.X q) (a : M.X (q + 1 + 1)) (b : N.X (q + 1))
    (du : M.d (q + 1) (q + 1 + 1) u = a)
    (dv : N.d q (q + 1) v = b + f.f (q + 1) u) :
    (mappingCone f).d q (q + 1) (complexConeElementMk A f q (-u) v) =
      complexConeElementMk A f (q + 1) a b := by
  apply complexConeElement_ext A f (q + 1)
  · rw [complexCone_d_fst, complexConeElementMk_fst, complexConeElementMk_fst,
      map_neg, du, neg_neg]
  · rw [complexCone_d_snd, complexConeElementMk_fst, complexConeElementMk_snd,
      complexConeElementMk_snd, map_neg, dv]
    abel

variable (σ : (Λ[3, 3] : SSet.{max u v}) ⟶ dgNerve A D)

/-- 実 cone の原始元の二座標から、元の実ホーンの型付き解を回収する。 -/
def dgLastHornSolutionOfConePrimitive (h : (dgLastHornResidualCone σ).X (-2))
    (dh : (dgLastHornResidualCone σ).d (-2) (-1) h = dgLastHornConeResidual σ) :
    DGLastHornSolution σ := by
  let φ := dgLastHornPostcomposition σ
  let u := (mappingCone.fst φ).val.v (-2) (-1) rfl h
  let a := (mappingCone.snd φ).v (-2) (-2) (by decide) h
  have hf : (homObject A D ((HornData.knownData σ).obj 0)
      ((HornData.knownData σ).obj 2)).d (-1) 0 (-u) =
      (mappingCone.fst φ).val.v (-1) 0 rfl (dgLastHornConeResidual σ) :=
    dgComplexConePrimitive_fst φ (-2) h (dgLastHornConeResidual σ) dh
  have hs : (homObject A D ((HornData.knownData σ).obj 0)
      ((HornData.knownData σ).obj 3)).d (-2) (-1) a =
      (mappingCone.snd φ).v (-1) (-1) (by decide) (dgLastHornConeResidual σ) +
        φ.f (-1) (-u) := dgComplexConePrimitive_snd φ (-2) h (dgLastHornConeResidual σ) dh
  exact ⟨-u, hf.trans (dgLastHornConeResidual_fst σ), a,
    hs.trans (congrArg₂ (· + ·) (dgLastHornConeResidual_snd σ)
      (dgLastHornPostcomposition_f σ (-1) (-u)))⟩

/-- 元の実ホーンの型付き解は、残差 cone の次数 −2 の原始元を与える。 -/
def dgLastHornConePrimitiveOfSolution (S : DGLastHornSolution σ) :
    (dgLastHornResidualCone σ).X (-2) :=
  complexConeElementMk A (dgLastHornPostcomposition σ) (-2) (-S.Q) S.a

/-- 二未知解から作った cone 成分の微分は、指定された二残差そのもの。 -/
lemma dgLastHornConePrimitiveOfSolution_differential (S : DGLastHornSolution σ) :
    (dgLastHornResidualCone σ).d (-2) (-1) (dgLastHornConePrimitiveOfSolution σ S) =
      dgLastHornConeResidual σ := by
  have da : (homObject A D ((HornData.knownData σ).obj 0)
      ((HornData.knownData σ).obj 3)).d (-2) (-1) S.a =
      dgLastHornTopResidual σ + (dgLastHornPostcomposition σ).f (-1) S.Q :=
    S.differential_a.trans (congrArg (dgLastHornTopResidual σ + ·)
      (dgLastHornPostcomposition_f σ (-1) S.Q).symm)
  have hg := dgComplexConeElementMk_differential (dgLastHornPostcomposition σ) (-2)
  exact hg S.Q S.a (dgLastHornMissingResidual σ) (dgLastHornTopResidual σ) S.differential_Q da

/-- 実ホーンの二未知解の存在は、実 cone の指定残差が境界であることと同値。 -/
lemma dgLastHornSolution_nonempty_iff_coneResidual_boundary :
    Nonempty (DGLastHornSolution σ) ↔
      ∃ h : (dgLastHornResidualCone σ).X (-2),
        (dgLastHornResidualCone σ).d (-2) (-1) h = dgLastHornConeResidual σ := by
  constructor
  · rintro ⟨S⟩
    exact ⟨dgLastHornConePrimitiveOfSolution σ S,
      dgLastHornConePrimitiveOfSolution_differential σ S⟩
  · rintro ⟨h, dh⟩
    exact ⟨dgLastHornSolutionOfConePrimitive σ h dh⟩

end SerrePositivity.InfinityCategories
