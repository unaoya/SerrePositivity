module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CofiberBoundaryJoinFiller
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CosliceBoundaryFromJoinFaces

/-! # cofiber の join 充填の境界面

概要：二セルを貼り合わせた写像が元の coslice 境界の全ての面を延長することを証明する。
方針：各セルの既知面の保存と二セルの押し出しの外延性を使う。
規約：HTT §1.2.13。使われ方：標準 cofiber 余錐の始対象性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable {S : Type u} [CommRing S] {A B C : _root_.SerrePositivity.DifferentialGraded.Complex S}

/-- Left 単体を表す写像の既知面は元の境界の制限。 -/
lemma cofiberBoundaryLeftSimplex_face_map {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberSquare f g)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberCocone f g))
    (j : Fin (n + 4)) (hj : j ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n) :
    SSet.stdSimplex.δ j ≫ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLeftSimplex f g b hb) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftLift n j hj ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b := by
  rw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
  apply SSet.yonedaEquiv.injective
  rw [Equiv.apply_symm_apply]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLeftSimplex_pullback_face f g b hb j hj

/-- Right 単体を表す写像の既知面は元の境界の制限。 -/
lemma cofiberBoundaryRightSimplex_face_map {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberSquare f g)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberCocone f g))
    (j : Fin (n + 4)) (hj : j ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n) :
    SSet.stdSimplex.δ j ≫ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRightSimplex f g b hb) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightLift n j hj ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b := by
  rw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
  apply SSet.yonedaEquiv.injective
  rw [Equiv.apply_symm_apply]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRightSimplex_pullback_face f g b hb j hj

/-- 貼合せた join 充填は元の coslice 境界の全ての面で一致する。 -/
lemma cofiberBoundaryJoinFiller_faces {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberSquare f g)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberCocone f g))
    (j : Fin (n + 2)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (SSet.horn 2 0 : SSet.{u + 1})) (SSet.stdSimplex.δ j) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryJoinFiller f g b hb =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (SSet.horn 2 0 : SSet.{u + 1})) (SSet.boundary.ι j) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b := by
  have hj : j.succ.succ ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n :=
    Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  have hidx : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaceIndex j.succ.succ hj = j := by
    apply Fin.ext
    change (j.val + 1 + 1) - 2 = j.val
    omega
  apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoin_isPushout n).hom_ext
  · rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoinLeft_face, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryJoinFiller_left,
      cofiberBoundaryLeftSimplex_face_map f g b hb j.succ.succ hj]
    simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftLift, hidx, Category.assoc]
  · rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoinRight_face, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryJoinFiller_right,
      cofiberBoundaryRightSimplex_face_map f g b hb j.succ.succ hj]
    simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightLift, hidx, Category.assoc]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
