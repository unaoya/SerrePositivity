module
public import SerrePositivity.EInfinity.BarrattEccles.CAlgForgetDerived
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.Reindexing.ConstantRestrictionArrow
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeFamilyUnderlying
/-!
概要：実 U の全源同型の定値制限を元の底の複体頂点へ比較する。
方針：同じ全源同型を評価し、通常忘却の零単体表示だけを輸送する。
規約：実 U と元の全源同型の二射を保持する。
使われ方：標準単位の全族公式と忘却後の屋根三角形の端点照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet MonoidalClosed
open SerrePositivity.InfinityCategories SerrePositivity.DifferentialGraded
open _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom
open scoped Simplicial
variable (A : Type u) [CommRing A] (B : CofibrantAlgebra A)

/-- 概要：cofibrant 相対入力の忘却値は元の底の複体の導来頂点。
方針：同じ零単体の通常忘却を計算する。
規約：頂点の表示だけの等式。使われ方：全源同型の端点輸送。 -/
lemma cofibrantUnderlying_ordinary_vertex :
    (cofibrantAlgebraUnderlyingDerivedSource A).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ULiftHom.objUp.{u + 1, u + 1} B)) =
    (_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex B.obj.carrier) := by
  apply congrArg ((_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A).app (Opposite.op ⦋0⦌))
  exact ComposableArrows.ext₀ rfl

/-- 概要：実 U の元の全源同型を、同じ底の複体頂点との実同型にする。
方針：同じ全二射の評価と通常忘却の零単体等式を合成する。
規約：比較射を選び直さない。使われ方：全族単位三角形の実端点。 -/
def cofibrantForgetOrdinaryVertexIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((cAlgForgetDerived A).app (Opposite.op ⦋0⦌)
      ((cAlgLocalizationSource A).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ULiftHom.objUp.{u + 1, u + 1} B))))
      ((_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex B.obj.carrier)) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.functorIsoEvaluate (cAlgForgetDerived_sourceIso A)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ULiftHom.objUp.{u + 1, u + 1} B)) ≪≫
      eqToIso (congrArg HomotopyCategory.mk (cofibrantUnderlying_ordinary_vertex A B))

variable (I : Type (u + 1)) [Category.{u + 1} I]

/-- 概要：元の全源同型の定値制限は同じ実頂点比較の定値族。
方針：元の全評価公式と同じ零単体の端点輸送を合成する。
規約：任意の全パラメータを保持。使われ方：屋根左端・右端の全族比較。 -/
lemma cofibrantForgetOrdinaryRestriction_hom_arrow :
    Arrow.mk (((cAlgForgetDerived_sourceIso A).precomp
      (nerveMap ((Functor.const I).obj (ULiftHom.objUp.{u + 1, u + 1} B)))).hom) =
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap (nerve I) (cofibrantForgetOrdinaryVertexIso A B).hom) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveMap_const]
  have h := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.constantRestriction_arrow (nerve I) (cAlgForgetDerived_sourceIso A).hom
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ULiftHom.objUp.{u + 1, u + 1} B))
  have ht := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.constantHom_transport_arrow (nerve I) rfl
    (cofibrantUnderlying_ordinary_vertex A B)
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (cAlgForgetDerived_sourceIso A).hom
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ULiftHom.objUp.{u + 1, u + 1} B)))
  exact h.trans (by simpa only [cofibrantForgetOrdinaryVertexIso, Iso.trans_hom,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.functorIsoEvaluate, eqToIso.hom, eqToHom_refl, Category.id_comp] using ht.symm)

end SerrePositivity.EInfinity.BarrattEccles
