module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCommaAugHomotopyComposition
/-!
概要：実比較 cochain の出力次数を等式で指定し、一般 HA 係数の次数輸送を明示する。
方針：同じ cochain の v 成分を使い、既証明の全微分式・合成式を輸送する。
規約：追加の cochain を選ばない。使われ方：切断・削除和で異なる中間次数をそろえる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E)
/-- 出力次数を指定した、同じ実比較 cochain の成分。 -/
def dgCommaAugmentationHomotopyAt (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F)
    (p q : ℤ) (h : p - 1 = q) (a : _root_.SerrePositivity.DifferentialGraded.GradedHom R X Y p) :
    _root_.SerrePositivity.DifferentialGraded.GradedHom R X.replacement (F.obj Y.source) q :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R C E F X Y).v p q (by omega) a
/-- 出力次数を指定しても、同じ実比較成分を保持する。 -/
lemma dgCommaAugmentationHomotopyAt_heq (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F)
    (p q : ℤ) (h : p - 1 = q) (a : _root_.SerrePositivity.DifferentialGraded.GradedHom R X Y p) :
    HEq (dgCommaAugmentationHomotopyAt R C E F X Y p q h a)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationHomotopyComponent R C E F X Y p a) := by
  subst q
  rfl
/-- 指定出力次数で読む、同じ全微分式。 -/
lemma dgCommaAugmentationHomotopyAt_differential
    (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F) (p q : ℤ) (h : p - 1 = q)
    (a : _root_.SerrePositivity.DifferentialGraded.GradedHom R X Y p) :
    (_root_.SerrePositivity.DifferentialGraded.homObject R E X.replacement (F.obj Y.source)).d q p
        (dgCommaAugmentationHomotopyAt R C E F X Y p q h a) +
      dgCommaAugmentationHomotopyAt R C E F X Y (p + 1) p (by omega)
        ((_root_.SerrePositivity.DifferentialGraded.homObject R _ X Y).d p (p + 1) a) +
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaBoundary R C E F X Y).f p a = 0 := by
  subst q
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationHomotopyComponent_differential R C E F X Y p a
/-- 中間次数を指定した、同じ通常順の比較合成則。 -/
lemma dgCommaAugmentationHomotopyAt_compose
    (X Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F) (p q n m : ℤ)
    (hsum : p + q = n) (h : n - 1 = m) (a : _root_.SerrePositivity.DifferentialGraded.GradedHom R X Y p) (b : _root_.SerrePositivity.DifferentialGraded.GradedHom R Y Z q) :
    dgCommaAugmentationHomotopyAt R C E F X Z n m h (_root_.SerrePositivity.DifferentialGraded.compose R b a hsum) =
      q.negOnePow • _root_.SerrePositivity.DifferentialGraded.compose R (x := X.replacement) (y := F.obj Y.source)
        (z := F.obj Z.source) (n := m)
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaImageHomMap R C E F Y Z).f q b)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationHomotopyComponent R C E F X Y p a) (by omega) +
      _root_.SerrePositivity.DifferentialGraded.compose R (x := X.replacement) (y := Y.replacement)
        (z := F.obj Z.source) (n := m)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationHomotopyComponent R C E F Y Z q b)
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R C E F X Y).f p a) (by omega) := by
  subst n
  subst m
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationHomotopyComponent_compose R C E F X Y Z p q a b
end SerrePositivity.InfinityCategories.Project.DerivedCategories
