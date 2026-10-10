module

public import SerrePositivity.CategoryTheory.HomologicalEuler

/-! # 零写像の錐のホモロジー長

錐の分裂同型を選ばず、長完全列から短完全列を取り出す。
cochain 添字では第 q 次の錐の長さは第 q 次と第 q+1 次の和になる。
-/

@[expose] public section

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {A : Type*} [Category* A] [Abelian A]
  (F : C ⥤ A) [F.IsHomological] [F.ShiftSequence ℤ]

/-- 第一射が零の完全三角形から得られるホモロジー短完全列。 -/
lemma homologySequence_shortExact_of_zero (T : Triangle C) (hT : T ∈ distTriang C)
    (hf : T.mor₁ = 0) (q : ℤ) :
    (ShortComplex.mk _ _ (F.comp_homologySequenceδ T hT q (q + 1) rfl)).ShortExact := by
  have hm : Mono ((F.shift q).map T.mor₂) :=
    (F.homologySequence_mono_shift_map_mor₂_iff T hT q).mpr (by rw [hf, Functor.map_zero])
  have he : Epi (F.homologySequenceδ T q (q + 1) rfl) :=
    (F.homologySequence_exact₁ T hT q (q + 1) rfl).epi_f_iff.mpr
      (by change (F.shift (q + 1)).map T.mor₁ = 0; rw [hf, Functor.map_zero])
  exact ⟨F.homologySequence_exact₃ T hT q (q + 1) rfl⟩

variable (l : A → ℝ)
  (ha : ∀ {S : ShortComplex A}, S.ShortExact → l S.X₂ = l S.X₁ + l S.X₃)

include ha in
/-- 零写像の錐の長さは、隣接する二次数の長さの和。 -/
lemma homologyLength_zero_cone (T : Triangle C) (hT : T ∈ distTriang C)
    (hf : T.mor₁ = 0) (q : ℤ) :
    l ((F.shift q).obj T.obj₃) =
      l ((F.shift q).obj T.obj₂) + l ((F.shift (q + 1)).obj T.obj₁) :=
  ha (homologySequence_shortExact_of_zero F T hT hf q)

end SerrePositivity
