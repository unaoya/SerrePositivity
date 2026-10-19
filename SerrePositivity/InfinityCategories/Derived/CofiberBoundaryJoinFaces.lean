module
public import SerrePositivity.InfinityCategories.Derived.CofiberBoundaryJoinFiller
public import SerrePositivity.InfinityCategories.Derived.CosliceBoundaryFromJoinFaces

/-! # cofiber の join 充填の境界面

概要：二セルを貼り合わせた写像が元の coslice 境界の全ての面を延長することを証明する。
方針：各セルの既知面の保存と二セルの押し出しの外延性を使う。
規約：HTT §1.2.13。使われ方：標準 cofiber 余錐の始対象性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
open scoped Simplicial
variable {S : Type u} [CommRing S] {A B C : Complex S}

/-- Left 単体を表す写像の既知面は元の境界の制限。 -/
lemma cofiberBoundaryLeftSimplex_face_map {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g))
    (j : Fin (n + 4)) (hj : j ∈ spanSuffixFaces n) :
    SSet.stdSimplex.δ j ≫ SSet.yonedaEquiv.symm (cofiberBoundaryLeftSimplex f g b hb) =
      spanBoundaryLeftLift n j hj ≫ sliceUnderUncurry b := by
  rw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
  apply SSet.yonedaEquiv.injective
  rw [Equiv.apply_symm_apply]
  exact cofiberBoundaryLeftSimplex_pullback_face f g b hb j hj

/-- Right 単体を表す写像の既知面は元の境界の制限。 -/
lemma cofiberBoundaryRightSimplex_face_map {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g))
    (j : Fin (n + 4)) (hj : j ∈ spanSuffixFaces n) :
    SSet.stdSimplex.δ j ≫ SSet.yonedaEquiv.symm (cofiberBoundaryRightSimplex f g b hb) =
      spanBoundaryRightLift n j hj ≫ sliceUnderUncurry b := by
  rw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
  apply SSet.yonedaEquiv.injective
  rw [Equiv.apply_symm_apply]
  exact cofiberBoundaryRightSimplex_pullback_face f g b hb j hj

/-- 貼合せた join 充填は元の coslice 境界の全ての面で一致する。 -/
lemma cofiberBoundaryJoinFiller_faces {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g))
    (j : Fin (n + 2)) :
    joinMap (𝟙 (SSet.horn 2 0 : SSet.{u + 1})) (SSet.stdSimplex.δ j) ≫
      cofiberBoundaryJoinFiller f g b hb =
    joinMap (𝟙 (SSet.horn 2 0 : SSet.{u + 1})) (SSet.boundary.ι j) ≫ sliceUnderUncurry b := by
  have hj : j.succ.succ ∈ spanSuffixFaces n :=
    Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  have hidx : spanSuffixFaceIndex j.succ.succ hj = j := by
    apply Fin.ext
    change (j.val + 1 + 1) - 2 = j.val
    omega
  apply (spanJoin_isPushout n).hom_ext
  · rw [← Category.assoc, ← spanJoinLeft_face, Category.assoc, cofiberBoundaryJoinFiller_left,
      cofiberBoundaryLeftSimplex_face_map f g b hb j.succ.succ hj]
    simp only [spanBoundaryLeftLift, hidx, Category.assoc]
  · rw [← Category.assoc, ← spanJoinRight_face, Category.assoc, cofiberBoundaryJoinFiller_right,
      cofiberBoundaryRightSimplex_face_map f g b hb j.succ.succ hj]
    simp only [spanBoundaryRightLift, hidx, Category.assoc]

end SerrePositivity.InfinityCategories
