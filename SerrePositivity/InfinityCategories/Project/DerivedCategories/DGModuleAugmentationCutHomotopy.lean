module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleAugmentationHomotopyAt
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleAugmentationCutDifferential
/-!
概要：元の実単体の切断合成へ比較 cochain を適用した値を、同じ二つの実補正へ分解する。
方針：出力次数を指定した全斉次合成則を、homOrZero の同じ左右二成分へ適用する。
規約：全整数次数・全内部切断を保持。使われ方：一般 HA 方程式の二重切断の相殺。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E))
  {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F) n)
/-- 左比較成分を元の実右入力像へ後合成する、全域切断係数。 -/
def dgModuleAugmentationImageCut (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (j : Fin (n + 1)) :
    _root_.SerrePositivity.DifferentialGraded.GradedHom R (s.obj a).replacement.val (F.obj (s.obj b).source) k :=
  if h : (2 - ((I.filter (· ≤ j)).card : ℤ) - 1) +
      (2 - ((I.filter (j ≤ ·)).card : ℤ)) = k then
    _root_.SerrePositivity.DifferentialGraded.compose R (x := (s.obj a).replacement.val) (y := F.obj (s.obj j).source)
      (z := F.obj (s.obj b).source)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionImageHomMap R C E F (s.obj j) (s.obj b)).f _
        (s.homOrZero (I.filter (j ≤ ·)) j b (2 - ((I.filter (j ≤ ·)).card : ℤ))))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationHomotopyComponent R C E F (s.obj a) (s.obj j) _
        (s.homOrZero (I.filter (· ≤ j)) a j (2 - ((I.filter (· ≤ j)).card : ℤ)))) h
  else 0
/-- 実入力切断合成の同じ比較成分は、左右の実補正の同じ符号付き和。 -/
lemma dgModuleAugmentationHomotopyAt_cutCompose
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (j : Fin (n + 1))
    (hsum : (2 - ((I.filter (· ≤ j)).card : ℤ)) +
      (2 - ((I.filter (j ≤ ·)).card : ℤ)) = k + 1) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationHomotopyAt R C E F (s.obj a) (s.obj b) (k + 1) k (by omega)
      (s.cutCompose I a b k j) =
    (2 - ((I.filter (j ≤ ·)).card : ℤ)).negOnePow •
      dgModuleAugmentationImageCut R C E F s I a b k j +
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationHomotopyCut R C E F s I a b k j := by
  have hL : (2 - ((I.filter (· ≤ j)).card : ℤ) - 1) +
      (2 - ((I.filter (j ≤ ·)).card : ℤ)) = k := by omega
  have hR : (2 - ((I.filter (· ≤ j)).card : ℤ)) +
      (2 - ((I.filter (j ≤ ·)).card : ℤ) - 1) = k := by omega
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cutCompose, dite_eq_left hsum,
    dgModuleAugmentationImageCut, dite_eq_left hL,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationHomotopyCut, dite_eq_left hR]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationHomotopyAt_compose R C E F (s.obj a) (s.obj j) (s.obj b)
    _ _ (k + 1) k hsum (by omega) _ _
end SerrePositivity.InfinityCategories.Project.DerivedCategories
