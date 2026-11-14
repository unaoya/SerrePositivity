module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.DGFunctors.DGFunctorCommaCategory
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.ComplexHomotopies.ComplexMinusOneCochainBoundary
/-!
概要：実 augmentation を比較する全 cochain を、全整数次数の斉次成分として回収する。
方針：同じ実比較 cochain の微分式と実単位の零式を評価する。
規約：全 Hom end の要素を保持。使われ方：実 augmentation prism の高次補正項。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded MonoidalCategory CochainComplex HomComplex
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
/-- 同じ実比較 cochain の、次数 n の斉次射への作用。 -/
def dgCommaAugmentationHomotopyComponent
    (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F) (n : ℤ)
    (a : GradedHom R X Y n) :
    (homObject R E X.replacement (F.obj Y.source)).X (n - 1) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R C E F X Y).v n (n - 1) (by omega) a
/-- 比較成分の二つの全微分項は、同じ実比較差の負になる。 -/
lemma dgCommaAugmentationHomotopyComponent_differential
    (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F) (n : ℤ) (a : GradedHom R X Y n) :
    (homObject R E X.replacement (F.obj Y.source)).d (n - 1) n
        (dgCommaAugmentationHomotopyComponent R C E F X Y n a) +
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R C E F X Y).v (n + 1) n (by omega)
        ((homObject R _ X Y).d n (n + 1) a) +
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaBoundary R C E F X Y).f n a = 0 :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMinusOneCochain_boundary_apply
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R C E F X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaBoundary R C E F X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive_boundary R C E F X Y) n a
/-- 実単位の全次数成分に対して、同じ比較 cochain は厳密に零。 -/
lemma dgCommaAugmentationHomotopyComponent_unit
    (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F) (n : ℤ)
    (a : (𝟙_ (Complex R)).X n) :
    dgCommaAugmentationHomotopyComponent R C E F X X n
      ((eId (Complex R) X).f n a) = 0 := by
  have he := Cochain.congr_v (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaIdentity_comparison R C E F X)
    n (n - 1) (by omega)
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComparison, Cochain.zero_cochain_comp_v,
    Cochain.ofHom_v, Cochain.zero_v] at he
  exact ConcreteCategory.congr_hom he a
/-- 同じ実比較 cochain の成分は、斉次射の和を保つ。 -/
lemma dgCommaAugmentationHomotopyComponent_add
    (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F) (n : ℤ) (a b : GradedHom R X Y n) :
    dgCommaAugmentationHomotopyComponent R C E F X Y n (a + b) =
      dgCommaAugmentationHomotopyComponent R C E F X Y n a +
        dgCommaAugmentationHomotopyComponent R C E F X Y n b :=
  map_add (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R C E F X Y).v n (n - 1) (by omega)).hom) a b
/-- 実比較成分は、符号単位によるスカラー作用を保つ。 -/
lemma dgCommaAugmentationHomotopyComponent_units_smul
    (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F) (n : ℤ)
    (s : ℤˣ) (a : GradedHom R X Y n) :
    dgCommaAugmentationHomotopyComponent R C E F X Y n (s • a) =
      s • dgCommaAugmentationHomotopyComponent R C E F X Y n a := by
  simp only [dgCommaAugmentationHomotopyComponent, Units.smul_def, map_zsmul]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
