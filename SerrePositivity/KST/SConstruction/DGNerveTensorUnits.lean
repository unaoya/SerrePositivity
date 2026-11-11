module
public import SerrePositivity.KST.SConstruction.CubicalLambdaNerveUnits
public import SerrePositivity.KST.SConstruction.DGNerveTensorNaturality

/-! # native dg nerve の元の増大による左右単位則
概要：元の一対象 A との実 tensor への左右単位挿入と、実単位関手による回収を示す。
方針：全作用素を保つ Λ 比較同型で元の増大による単位挿入を移す。
規約：一対象圏を拡大せず入力の対象宇宙を保持。使われ方：native tensor 比較の単位。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Opposite Simplicial SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 元の一対象 A を左に挿入する、native dg nerve の実単体的写像。 -/
def dgNerveUnitLeft : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (DGTensorCategory A PUnit.{1} D) :=
  (cubicalLambdaNerveNativeIso A D).inv ≫ cubicalLambdaNerveUnitLeft A D ≫
    (cubicalLambdaNerveNativeIso A (DGTensorCategory A PUnit.{1} D)).hom

/-- 元の一対象 A を右に挿入する、native dg nerve の実単体的写像。 -/
def dgNerveUnitRight : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (DGTensorCategory A D PUnit.{1}) :=
  (cubicalLambdaNerveNativeIso A D).inv ≫ cubicalLambdaNerveUnitRight A D ≫
    (cubicalLambdaNerveNativeIso A (DGTensorCategory A D PUnit.{1})).hom

/-- native 左単位挿入の各単体は、元の増大と元の実逆 dg 関手の組。 -/
lemma dgNerveUnitLeft_app {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D N) :
    (dgNerveUnitLeft A D).app (op ⦋N⦌) s = cubicalLambdaNativeSimplex A
      (cubicalLambdaFunctorPair A (cubicalLambdaCounit A (Δ[N] : SSet.{u}))
        (simplexHAInverseFunctor A s)) := rfl

/-- native 右単位挿入の各単体は、元の実逆 dg 関手と元の増大の組。 -/
lemma dgNerveUnitRight_app {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D N) :
    (dgNerveUnitRight A D).app (op ⦋N⦌) s = cubicalLambdaNativeSimplex A
      (cubicalLambdaFunctorPair A (simplexHAInverseFunctor A s)
        (cubicalLambdaCounit A (Δ[N] : SSet.{u}))) := rfl

/-- native 左単位挿入は、元の実左単位 dg 関手で全単体的恒等を回収する。 -/
lemma dgNerveUnitLeft_unitor :
    dgNerveUnitLeft A D ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgTensorLeftUnitor A D) = 𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) := by
  ext n s
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D n.unop.len at s
  change (cubicalLambdaNativeSimplex A
    (cubicalLambdaFunctorPair A (cubicalLambdaCounit A (SSet.stdSimplex.obj n.unop))
      (simplexHAInverseFunctor A s))).map (dgTensorLeftUnitor A D) = s
  rw [← cubicalLambdaNativeSimplex_post, cubicalLambdaFunctorPair_left_unit,
    cubicalLambdaNativeSimplex_inverse]

/-- native 右単位挿入は、元の実右単位 dg 関手で全単体的恒等を回収する。 -/
lemma dgNerveUnitRight_unitor :
    dgNerveUnitRight A D ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgTensorRightUnitor A D) = 𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) := by
  ext n s
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D n.unop.len at s
  change (cubicalLambdaNativeSimplex A
    (cubicalLambdaFunctorPair A (simplexHAInverseFunctor A s)
      (cubicalLambdaCounit A (SSet.stdSimplex.obj n.unop)))).map (dgTensorRightUnitor A D) = s
  rw [← cubicalLambdaNativeSimplex_post, cubicalLambdaFunctorPair_right_unit,
    cubicalLambdaNativeSimplex_inverse]

end SerrePositivity.KST.SConstruction
