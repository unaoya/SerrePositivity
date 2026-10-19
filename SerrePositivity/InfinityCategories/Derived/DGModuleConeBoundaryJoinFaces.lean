module
public import SerrePositivity.InfinityCategories.Derived.DGModuleConeBoundaryJoinFiller
public import SerrePositivity.InfinityCategories.Derived.CosliceBoundaryFromJoinFaces

/-! # cofiber の join 充填の境界面

概要：二セルを貼り合わせた写像が元の coslice 境界の全ての面を延長することを証明する。
方針：各セルの既知面の保存と二セルの押し出しの外延性を使う。
規約：HTT §1.2.13。使われ方：標準 cofiber 余錐の始対象性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {M N : ModuleCategory A D}

/-- Left 単体を表す写像の既知面は元の境界の制限。 -/
lemma dgModuleConeBoundaryLeftSimplex_face_map {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceUnder (pushoutSpan (dgModuleConeSquare A D f)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (dgModuleConeCocone A D f))
    (j : Fin (n + 4)) (hj : j ∈ spanSuffixFaces n) :
    SSet.stdSimplex.δ j ≫ SSet.yonedaEquiv.symm (dgModuleConeBoundaryLeftSimplex A D f b hb) =
      spanBoundaryLeftLift n j hj ≫ sliceUnderUncurry b := by
  rw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
  apply SSet.yonedaEquiv.injective
  rw [Equiv.apply_symm_apply]
  exact dgModuleConeBoundaryLeftSimplex_pullback_face A D f b hb j hj

/-- Right 単体を表す写像の既知面は元の境界の制限。 -/
lemma dgModuleConeBoundaryRightSimplex_face_map {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceUnder (pushoutSpan (dgModuleConeSquare A D f)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (dgModuleConeCocone A D f))
    (j : Fin (n + 4)) (hj : j ∈ spanSuffixFaces n) :
    SSet.stdSimplex.δ j ≫ SSet.yonedaEquiv.symm (dgModuleConeBoundaryRightSimplex A D f b hb) =
      spanBoundaryRightLift n j hj ≫ sliceUnderUncurry b := by
  rw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
  apply SSet.yonedaEquiv.injective
  rw [Equiv.apply_symm_apply]
  exact dgModuleConeBoundaryRightSimplex_pullback_face A D f b hb j hj

/-- 貼合せた join 充填は元の coslice 境界の全ての面で一致する。 -/
lemma dgModuleConeBoundaryJoinFiller_faces {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceUnder (pushoutSpan (dgModuleConeSquare A D f)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (dgModuleConeCocone A D f))
    (j : Fin (n + 2)) :
    joinMap (𝟙 (SSet.horn 2 0 : SSet)) (SSet.stdSimplex.δ j) ≫
      dgModuleConeBoundaryJoinFiller A D f b hb =
    joinMap (𝟙 (SSet.horn 2 0 : SSet)) (SSet.boundary.ι j) ≫ sliceUnderUncurry b := by
  have hj : j.succ.succ ∈ spanSuffixFaces n :=
    Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  have hidx : spanSuffixFaceIndex j.succ.succ hj = j := by
    apply Fin.ext
    change (j.val + 1 + 1) - 2 = j.val
    omega
  apply (spanJoin_isPushout n).hom_ext
  · rw [← Category.assoc, ← spanJoinLeft_face, Category.assoc, dgModuleConeBoundaryJoinFiller_left,
      dgModuleConeBoundaryLeftSimplex_face_map A D f b hb j.succ.succ hj]
    simp only [spanBoundaryLeftLift, hidx, Category.assoc]
  · rw [← Category.assoc, ← spanJoinRight_face, Category.assoc,
    dgModuleConeBoundaryJoinFiller_right,
      dgModuleConeBoundaryRightSimplex_face_map A D f b hb j.succ.succ hj]
    simp only [spanBoundaryRightLift, hidx, Category.assoc]

end SerrePositivity.InfinityCategories
