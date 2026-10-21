module
public import SerrePositivity.InfinityCategories.Derived.DGCommaAugHomotopyComposition
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
/-- 出力次数を指定した、同じ実比較 cochain の成分。 -/
def dgCommaAugmentationHomotopyAt (X Y : DGFunctorCommaObject R C E F)
    (p q : ℤ) (h : p - 1 = q) (a : GradedHom R X Y p) :
    GradedHom R X.replacement (F.obj Y.source) q :=
  (dgFunctorCommaPrimitive R C E F X Y).v p q (by omega) a
/-- 出力次数を指定しても、同じ実比較成分を保持する。 -/
lemma dgCommaAugmentationHomotopyAt_heq (X Y : DGFunctorCommaObject R C E F)
    (p q : ℤ) (h : p - 1 = q) (a : GradedHom R X Y p) :
    HEq (dgCommaAugmentationHomotopyAt R C E F X Y p q h a)
      (dgCommaAugmentationHomotopyComponent R C E F X Y p a) := by
  subst q
  rfl
/-- 指定出力次数で読む、同じ全微分式。 -/
lemma dgCommaAugmentationHomotopyAt_differential
    (X Y : DGFunctorCommaObject R C E F) (p q : ℤ) (h : p - 1 = q)
    (a : GradedHom R X Y p) :
    (homObject R E X.replacement (F.obj Y.source)).d q p
        (dgCommaAugmentationHomotopyAt R C E F X Y p q h a) +
      dgCommaAugmentationHomotopyAt R C E F X Y (p + 1) p (by omega)
        ((homObject R _ X Y).d p (p + 1) a) +
      (dgFunctorCommaBoundary R C E F X Y).f p a = 0 := by
  subst q
  exact dgCommaAugmentationHomotopyComponent_differential R C E F X Y p a
/-- 中間次数を指定した、同じ通常順の比較合成則。 -/
lemma dgCommaAugmentationHomotopyAt_compose
    (X Y Z : DGFunctorCommaObject R C E F) (p q n m : ℤ)
    (hsum : p + q = n) (h : n - 1 = m) (a : GradedHom R X Y p) (b : GradedHom R Y Z q) :
    dgCommaAugmentationHomotopyAt R C E F X Z n m h (compose R b a hsum) =
      q.negOnePow • compose R (x := X.replacement) (y := F.obj Y.source)
        (z := F.obj Z.source) (n := m)
        ((dgFunctorCommaImageHomMap R C E F Y Z).f q b)
        (dgCommaAugmentationHomotopyComponent R C E F X Y p a) (by omega) +
      compose R (x := X.replacement) (y := Y.replacement)
        (z := F.obj Z.source) (n := m)
        (dgCommaAugmentationHomotopyComponent R C E F Y Z q b)
        ((dgFunctorCommaReplacementHomMap R C E F X Y).f p a) (by omega) := by
  subst n
  subst m
  exact dgCommaAugmentationHomotopyComponent_compose R C E F X Y Z p q a b
end SerrePositivity.InfinityCategories
