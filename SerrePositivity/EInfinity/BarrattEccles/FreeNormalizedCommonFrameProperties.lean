module
public import SerrePositivity.EInfinity.BarrattEccles.FreeNormalizedHomFrames
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Resolution
/-! 概要：標準自由 Hom と正規化 Hom の同じ共通 frame の実比較射を保持する。
方針：既存の FrameOverFunctor の実左右射と augmentation をそのまま代入する。
規約：同じ自由 probe・元の全左右射を保持し、モデル構造を局所的に選ぶ。
使われ方：元の四列比較による全 pinched 族の弱同値性の検出。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Limits HomotopicalAlgebra
open SerrePositivity.DifferentialGraded SerrePositivity.Reedy

variable (A : Type u) [CommRing A]

/-- 概要：同じ共通 frame から元の正規化 frame への全比較射。
方針：元の共通 cofibrant 置換の右射を使う。
規約：元の全射を保持。使われ方：四列比較の右側。 -/
def freeNormalizedCommonFrameRight : freeNormalizedCommonFrame A ⟶ freeNormalizedProbeFrame A := by
  let := modelCategory A
  exact FrameOverFunctor.right (mappingCofibrantFactorization A)
    (cosimplicialResolutionFamily (mappingCofibrantFactorization A))
    (freeProbeFunctor A) (freeNormalizedProbeFrame A) (freeNormalizedProbeAugmentation A)

/-- 概要：同じ共通 frame の元の自由 probe への augmentation。
方針：元の右射と正規化 augmentation を合成する。
規約：同じ全自然変換を保持。使われ方：共通 frame の実屋根。 -/
def freeNormalizedCommonFrameAugmentation :
    freeNormalizedCommonFrame A ⟶ freeProbeFunctor A ⋙ Functor.const SimplexCategory :=
  freeNormalizedCommonFrameRight A ≫ freeNormalizedProbeAugmentation A

/-- 概要：同じ共通 frame から元の標準自由 frame への全比較射。
方針：元の共通 cofibrant 置換の左射を使う。
規約：同じ全射を保持。使われ方：四列比較の標準側。 -/
def freeNormalizedCommonFrameLeft :
    let := modelCategory A
    freeNormalizedCommonFrame A ⟶ freeProbeFunctor A ⋙
      (cosimplicialResolutionFamily (mappingCofibrantFactorization A)).obj := by
  let := modelCategory A
  exact FrameOverFunctor.left (mappingCofibrantFactorization A)
    (cosimplicialResolutionFamily (mappingCofibrantFactorization A))
    (freeProbeFunctor A) (freeNormalizedProbeFrame A) (freeNormalizedProbeAugmentation A)

/-- 概要：元の標準左射と augmentation の全三角形。
方針：元の共通置換の over 方程式を使う。
規約：同じ全自然変換を保持。使われ方：同じ始域の四列比較。 -/
lemma freeNormalizedCommonFrameLeft_over :
    let := modelCategory A
    freeNormalizedCommonFrameLeft A ≫ Functor.whiskerLeft (freeProbeFunctor A)
      (cosimplicialResolutionFamily (mappingCofibrantFactorization A)).augmentation =
      freeNormalizedCommonFrameAugmentation A := by
  let := modelCategory A
  exact FrameOverFunctor.over (mappingCofibrantFactorization A)
    (cosimplicialResolutionFamily (mappingCofibrantFactorization A))
    (freeProbeFunctor A) (freeNormalizedProbeFrame A) (freeNormalizedProbeAugmentation A)

/-- 概要：元の共通左射の全次数での弱同値性。
方針：元の全 augmentation の弱同値性を既存の共通置換へ代入する。
規約：同じ全射を保持。使われ方：標準 Hom span の比較。 -/
lemma freeNormalizedCommonFrameLeft_weak (X : Complex A) (n : SimplexCategory) :
    let := modelCategory A
    weakEquivalences (operad A).Algebra (((freeNormalizedCommonFrameLeft A).app X).app n) := by
  let := modelCategory A
  exact FrameOverFunctor.left_weakEquivalence (mappingCofibrantFactorization A)
    (cosimplicialResolutionFamily (mappingCofibrantFactorization A))
    (freeProbeFunctor A) (freeNormalizedProbeFrame A) (freeNormalizedProbeAugmentation A)
    (freeNormalizedProbeAugmentation_weak A) X n

/-- 概要：元の共通右射の全次数での弱同値性。
方針：元の共通置換の右 trivial fibration 性を使う。
規約：追加の標数仮定を置かない。使われ方：全縦弱同値の供給。 -/
lemma freeNormalizedCommonFrameRight_weak (X : Complex A) (n : SimplexCategory) :
    let := modelCategory A
    weakEquivalences (operad A).Algebra (((freeNormalizedCommonFrameRight A).app X).app n) := by
  let := modelCategory A
  exact FrameOverFunctor.right_weakEquivalence (mappingCofibrantFactorization A)
    (cosimplicialResolutionFamily (mappingCofibrantFactorization A))
    (freeProbeFunctor A) (freeNormalizedProbeFrame A) (freeNormalizedProbeAugmentation A) X n

/-- 概要：同じ共通 frame の全 augmentation は弱同値。
方針：元の二つの弱射を合成する。
規約：同じ自由 probe を保持。使われ方：共通 roof の左脚。 -/
lemma freeNormalizedCommonFrameAugmentation_weak (X : Complex A) (n : SimplexCategory) :
    let := modelCategory A
    weakEquivalences (operad A).Algebra
      (((freeNormalizedCommonFrameAugmentation A).app X).app n) := by
  let := modelCategory A
  exact (weakEquivalences (operad A).Algebra).comp_mem _ _
    (freeNormalizedCommonFrameRight_weak A X n) (freeNormalizedProbeAugmentation_weak A X n)

/-- 概要：同じ共通 frame の実 Reedy cofibrancy。
方針：元の共通置換の cofibrancy を使う。
規約：元の複体に cofibrancy を要求しない。使われ方：全対象の cofibrant 持ち上げ。 -/
lemma freeNormalizedCommonFrame_cofibrant (X : Complex A) :
    let := modelCategory A
    reedyLeft simplex (cofibrations (operad A).Algebra)
      (initial.to ((freeNormalizedCommonFrame A).obj X)) := by
  let := modelCategory A
  exact FrameOverFunctor.commonObj_cofibrant (mappingCofibrantFactorization A)
    (cosimplicialResolutionFamily (mappingCofibrantFactorization A))
    (freeProbeFunctor A) (freeNormalizedProbeFrame A) (freeNormalizedProbeAugmentation A) X

/-- 概要：同じ共通 frame の全作用素は弱同値。
方針：同じ全 augmentation の比較を元の共通 frame に代入する。
規約：全作用素を保持。使われ方：全列の縦弱同値。 -/
lemma freeNormalizedCommonFrame_map_weak (X : Complex A) {n m : SimplexCategory} (f : n ⟶ m) :
    let := modelCategory A
    weakEquivalences (operad A).Algebra (((freeNormalizedCommonFrame A).obj X).map f) := by
  let := modelCategory A
  exact FrameOverFunctor.commonObj_homotopicallyConstant (mappingCofibrantFactorization A)
    (cosimplicialResolutionFamily (mappingCofibrantFactorization A))
    (freeProbeFunctor A) (freeNormalizedProbeFrame A) (freeNormalizedProbeAugmentation A)
    (freeNormalizedProbeAugmentation_weak A) X f

/-- 概要：同じ共通 frame の各対象は元の代数モデルで cofibrant。
方針：実 Reedy cofibrancy を各評価に適用する。
規約：元の同じ対象を保持。使われ方：cofibrant 相対圏の全列比較。 -/
lemma freeNormalizedCommonFrame_obj_cofibrant (X : Complex A) (n : SimplexCategory) :
    let := modelCategory A
    IsCofibrant (((freeNormalizedCommonFrame A).obj X).obj n) := by
  let := modelCategory A
  have hi : Cofibration ((initial.to ((freeNormalizedCommonFrame A).obj X)).app n) :=
    ⟨cofibration_app simplex (initial.to ((freeNormalizedCommonFrame A).obj X))
      (freeNormalizedCommonFrame_cofibrant A X) n⟩
  exact (isCofibrant_iff_of_isInitial ((initial.to ((freeNormalizedCommonFrame A).obj X)).app n)
    (initialIsInitial.isInitialObj ((evaluation SimplexCategory (operad A).Algebra).obj n)
      (⊥_ (SimplexCategory ⥤ (operad A).Algebra)))).mpr hi

end SerrePositivity.EInfinity.BarrattEccles
