module

public import SerrePositivity.InfinityCategories.F1.LeftStrictTransportEvaluation
public import SerrePositivity.InfinityCategories.F1.RelativeFunctorInitialEvaluation
public import SerrePositivity.InfinityCategories.Core.NerveCone
public import SerrePositivity.InfinityCategories.Core.TrivialFibrationEquivalence

/-!
概要：Kan 値 strict transport の恒等射評価は元の fiber への同値。
方針：undercategory の恒等射が始対象であることを、相対関手の点への制限に適用する。
規約：評価は全境界を持ち上げ、その各頂点の逆像は可縮な Kan 複体となる。
使われ方：Kerodon §5.3.1、strict transport と元の left fibration の fiber の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：strict transport の恒等射での評価は trivial Kan fibration。
方針：始対象 id_c の nerve の点包含の left anodyne 性から相対評価を持ち上げる。
規約：通常の圏 C は任意で、有限性は要求しない。
使われ方：Kerodon §5.3.1、strict transport の値の比較と選択空間の可縮性。 -/
instance leftStrictTransportEvaluate_trivialKanFibration
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] (c : C) :
    TrivialKanFibration (leftStrictTransportEvaluate p c) := by
  let i := nervePoint (Under.mk (𝟙 c))
  have hi : leftAnodyneExtensions i := nervePoint_leftAnodyne (Under.mkIdInitial (X := c))
  have hv : i.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0) =
      strictTransportUnderIdentityVertex c := by
    dsimp only [i, nervePoint]
    rw [SSet.yonedaEquiv_symm_zero]
    change PinchedHom.constant (nerveVertex (Under.mk (𝟙 c))) 0 = _
    rw [pinchedConstant_zero]
    rfl
  have he := relativeFunctorEvaluate_trivialKanFibration_of_pointMap p
    (nerveMap (Under.forget c)) i hi
  rw [hv] at he
  exact relativeFunctorEvaluate_trivialKanFibration_of_identification p
    (nerveMap (Under.forget c)) (strictTransportUnderIdentityVertex c)
    ((nerveEquiv (C := C)).symm c) (strictTransportUnderIdentityVertex_projection c)
    (leftStrictTransportEvaluate p c) (leftStrictTransportEvaluate_ι p c) he

/-- 概要：strict transport の恒等射での評価は quasicategory の同値。
方針：全境界持ち上げによる同値判定を適用する。
規約：評価射そのものの性質を示し、別の比較射に置き換えない。
使われ方：Kerodon §5.3.1、strict transport の値と元の fiber の同値。 -/
lemma leftStrictTransportEvaluate_isQCatEquivalence
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] (c : C) :
    IsQCatEquivalence (leftStrictTransportEvaluate p c) :=
  isQCatEquivalence_of_trivialKanFibration _

/-- 概要：strict transport の値と元の fibration の fiber の明示的な圏同値。
方針：恒等射評価の同値性から逆データを選ぶ。
規約：順方向の射は恒等射評価。
使われ方：Kerodon §5.3.1、strict transport 表現による fiber の回収。 -/
noncomputable def leftStrictTransportFiberEquivalence
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] (c : C) :
    QCatEquivalence (leftStrictTransport p c)
      (vertexFiber p ((nerveEquiv (C := C)).symm c)) :=
  (leftStrictTransportEvaluate_isQCatEquivalence p c).choose

/-- 概要：恒等射での値を指定した strict transport の選択空間は可縮な Kan 複体。
方針：trivial Kan fibration の各頂点 fiber の可縮性を使う。
規約：値の頂点 e は元の fibration の c 上の fiber に属する。
使われ方：Kerodon §5.3.1、strict transport による延長の高次の一意性。 -/
lemma leftStrictTransportEvaluate_fiber_isContractibleKan
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] (c : C)
    (e : (vertexFiber p ((nerveEquiv (C := C)).symm c)) _⦋0⦌) :
    IsContractibleKan (vertexFiber (leftStrictTransportEvaluate p c) e) :=
  vertexFiber_isContractibleKan _ e

end SerrePositivity.InfinityCategories
