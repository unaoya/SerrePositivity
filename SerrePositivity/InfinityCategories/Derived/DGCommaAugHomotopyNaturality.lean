module
public import SerrePositivity.InfinityCategories.Derived.DGCommaAugPrismData
public import SerrePositivity.InfinityCategories.Derived.DGGradedPrecompositionWhisker
public import SerrePositivity.InfinityCategories.Derived.DGClosedPostcompositionComponents
/-!
概要：同じ実比較差を通常順の augmentation 合成へ移し、閉辺の自然性ホモトピーを得る。
方針：全 Hom の前後合成の実成分公式と、同じ比較 cochain の微分式を使う。
規約：選び直したホモトピーを導入しない。使われ方：混合三角形の HA 方程式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded MonoidalCategory DGNerve
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
  (X Y : DGFunctorCommaObject R C E F)
/-- 全整数次数で、実比較差は通常順の同じ augmentation 合成の差。 -/
lemma dgCommaAugmentationBoundary_apply (n : ℤ) (a : GradedHom R X Y n) :
    (dgFunctorCommaBoundary R C E F X Y).f n a =
      compose R (x := X.replacement) (y := F.obj X.source) (z := F.obj Y.source)
        ((dgFunctorCommaImageHomMap R C E F X Y).f n a)
        (dgCommaAugmentationComponent R C E F X).val (zero_add n) -
      compose R (x := X.replacement) (y := Y.replacement) (z := F.obj Y.source)
        (dgCommaAugmentationComponent R C E F Y).val
        ((dgFunctorCommaReplacementHomMap R C E F X Y).f n a) (add_zero n) := by
  have hp := (dgGradedPrecompose_eq_whisker_f R E (q := X.replacement)
    (x := F.obj X.source) (y := F.obj Y.source) n
    ((dgFunctorCommaImageHomMap R C E F X Y).f n a) X.augmentation).symm
  have hq := dgClosedPostcomposition_f R E (x := X.replacement)
    (y := Y.replacement) (z := F.obj Y.source) Y.augmentation n
    ((dgFunctorCommaReplacementHomMap R C E F X Y).f n a)
  exact congrArg₂ (fun (x y : GradedHom R X.replacement (F.obj Y.source) n) => x - y) hp hq
/-- 閉次数零の同じ実射に対し、augmentation の自然性を比較する同じ実ホモトピー。 -/
lemma dgCommaAugmentationHomotopyComponent_closed_zero
    (a : GradedHom R X Y 0) (ha : differential R a = 0) :
    differential R (x := X.replacement) (y := F.obj Y.source)
      (dgCommaAugmentationHomotopyComponent R C E F X Y 0 a) =
      compose R (x := X.replacement) (y := Y.replacement) (z := F.obj Y.source)
        (dgCommaAugmentationComponent R C E F Y).val
        ((dgFunctorCommaReplacementHomMap R C E F X Y).f 0 a) (by omega) -
      compose R (x := X.replacement) (y := F.obj X.source) (z := F.obj Y.source)
        ((dgFunctorCommaImageHomMap R C E F X Y).f 0 a)
        (dgCommaAugmentationComponent R C E F X).val (by omega) := by
  have he := complexMinusOneCochain_boundary_closed_zero
    (dgFunctorCommaPrimitive R C E F X Y)
    (dgFunctorCommaBoundary R C E F X Y)
    (dgFunctorCommaPrimitive_boundary R C E F X Y) a ha
  have hb := congrArg Neg.neg (dgCommaAugmentationBoundary_apply R C E F X Y 0 a)
  exact he.trans (hb.trans (neg_sub _ _))
end SerrePositivity.InfinityCategories
