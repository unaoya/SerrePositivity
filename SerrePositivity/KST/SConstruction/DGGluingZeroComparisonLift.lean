module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.Projections
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomComplexes.Models.HomCalculus

/-! # 比較標的が実零である gluing Hom の指定持ち上げ
概要：元の比較標的が実零なら、指定した両鎖写像を零比較で同じ gluing Hom へ持ち上げる。
方針：元の比較差を零標的で消し、既存の実持ち上げと射影回収を使う。
規約：同じ二成分と全比較 cochain を保持。使われ方：二軸分解の元の二射。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
  (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) (hT : IsZero (M.value X.left Y.right))
  (K : Complex R) (a : K ⟶ homObject R C X.left Y.left)
  (b : K ⟶ homObject R D X.right Y.right)

include hT in
/-- 実零比較標的では、元の二鎖写像の零比較が同じ境界式を満たす。 -/
lemma dgGluingZeroComparison_boundary :
    δ (-1) 0 (0 : Cochain K (M.value X.left Y.right) (-1)) +
      Cochain.ofHom (biprod.lift a b ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDifference R C D M X Y) = 0 := by
  rw [hT.eq_of_tgt (biprod.lift a b ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDifference R C D M X Y) 0]
  simp

/-- 元の同じ二成分と零比較を持つ、実零比較標的への全パラメータ持ち上げ。 -/
def dgGluingZeroComparisonLift : K ⟶ homObject R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) X Y :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomLift R C D M X Y K a b 0
    (dgGluingZeroComparison_boundary R C D M X Y hT K a b)

/-- 同じ持ち上げの左射影は、元の同じ左鎖写像。 -/
lemma dgGluingZeroComparisonLift_left :
    dgGluingZeroComparisonLift R C D M X Y hT K a b ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap R C D M X Y = a :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomLift_left R C D M X Y K a b 0 _

/-- 同じ持ち上げの右射影は、元の同じ右鎖写像。 -/
lemma dgGluingZeroComparisonLift_right :
    dgGluingZeroComparisonLift R C D M X Y hT K a b ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomMap R C D M X Y = b :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomLift_right R C D M X Y K a b 0 _

/-- 同じ持ち上げの比較 cochain は、元の指定した零そのもの。 -/
lemma dgGluingZeroComparisonLift_comparison :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComparison R C D M X Y K
      (dgGluingZeroComparisonLift R C D M X Y hT K a b) = 0 :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomLift_comparison R C D M X Y K a b 0 _

end SerrePositivity.KST.SConstruction
