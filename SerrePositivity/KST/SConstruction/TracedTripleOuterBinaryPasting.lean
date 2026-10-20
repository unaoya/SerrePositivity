module
public import SerrePositivity.KST.SConstruction.TracedTripleNormalizedPasting
public import SerrePositivity.KST.SConstruction.OuterBinaryPasting

/-! # 元の全比較複体へ両外側全二部分面を厳密に接続する
概要：元の六面・両円柱に、元の左右外側二部分三角形全体を同じ全ホーンで貼る。
方針：正規化出口・隣接補正辺・最初の補正辺の厳密な回収式を使う。
規約：元の全八二単体と両全円柱を保持し、全三角形を取り替えない。
使われ方：元の左右外側段三角形を同じ対角補正辺で貼る。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet Spectra
open scoped Simplicial
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {w x y z : I} (f : w ⟶ x) (g : x ⟶ y) (h : y ⟶ z)

/-- 元の両外側全二部分面を、同じ六面・両全円柱の比較へ貼った実写像。 -/
def monicKTracedTripleOuterBinaryPasting (n : ℕ) :
    outerBinaryPasting.{u} ⟶
      (PointedObject.basedHom ((kOmegaSpectrum (F.obj w)).level n).space
        ((kKanSequence (F.obj z)).level n).space).right :=
  outerBinaryPastingMap (monicKTracedTripleNormalizedPasting F f g h n)
    (SSet.yonedaEquiv.symm (monicKPrismCompositeBinaryPointTriangle F (f ≫ g) h n).simplex)
    (SSet.yonedaEquiv.symm (monicKPrismCompositeBinaryPointTriangle F f (g ≫ h) n).simplex)
    (monicKTracedTripleNormalizedPasting_left_target F f g h n)
    (by
      rw [correctionOuterLeftSecond]
      simp only [Category.assoc]
      rw [monicKTracedTripleNormalizedPasting_original]
      exact monicKTracedTripleInterchangePasting_left_correction F f g h n)
    (by
      rw [correctionOuterRightFirst]
      simp only [Category.assoc]
      rw [monicKTracedTripleNormalizedPasting_original]
      exact monicKTracedTripleInterchangePasting_first_path F f g h n)
    (monicKTracedTripleNormalizedPasting_right_target F f g h n)

/-- 元の六面・両全正規化円柱の比較全体を厳密に回収する。 -/
lemma monicKTracedTripleOuterBinaryPasting_original (n : ℕ) :
    outerBinaryPastingOriginal ≫ monicKTracedTripleOuterBinaryPasting F f g h n =
      monicKTracedTripleNormalizedPasting F f g h n :=
  outerBinaryPastingMap_original _ _ _ _ _ _ _

/-- 元の左外側全二部分三角形そのものを厳密に回収する。 -/
lemma monicKTracedTripleOuterBinaryPasting_left (n : ℕ) :
    outerBinaryPastingLeftCell ≫ monicKTracedTripleOuterBinaryPasting F f g h n =
      SSet.yonedaEquiv.symm (monicKPrismCompositeBinaryPointTriangle F (f ≫ g) h n).simplex :=
  outerBinaryPastingMap_left _ _ _ _ _ _ _

/-- 元の右外側全二部分三角形そのものも厳密に回収する。 -/
lemma monicKTracedTripleOuterBinaryPasting_right (n : ℕ) :
    outerBinaryPastingRightCell ≫ monicKTracedTripleOuterBinaryPasting F f g h n =
      SSet.yonedaEquiv.symm (monicKPrismCompositeBinaryPointTriangle F f (g ≫ h) n).simplex :=
  outerBinaryPastingMap_right _ _ _ _ _ _ _

/-- 左の対角全辺は、元の左外側段三角形の同じ全合成補正辺。 -/
lemma monicKTracedTripleOuterBinaryPasting_left_direct (n : ℕ) :
    stdSimplex.δ 1 ≫ outerBinaryPastingLeftCell ≫
        monicKTracedTripleOuterBinaryPasting F f g h n =
      SSet.yonedaEquiv.symm
        (monicKTracedCompositionStageTriangleData F (f ≫ g) h n).direct.edge := by
  rw [monicKTracedTripleOuterBinaryPasting_left]
  exact monicKPrismCompositeBinaryPointTriangle_direct F (f ≫ g) h n

/-- 右の対角全辺も、元の右外側段三角形の同じ全合成補正辺。 -/
lemma monicKTracedTripleOuterBinaryPasting_right_direct (n : ℕ) :
    stdSimplex.δ 1 ≫ outerBinaryPastingRightCell ≫
        monicKTracedTripleOuterBinaryPasting F f g h n =
      SSet.yonedaEquiv.symm
        (monicKTracedCompositionStageTriangleData F f (g ≫ h) n).direct.edge := by
  rw [monicKTracedTripleOuterBinaryPasting_right]
  exact monicKPrismCompositeBinaryPointTriangle_direct F f (g ≫ h) n

end SerrePositivity.KST.SConstruction
