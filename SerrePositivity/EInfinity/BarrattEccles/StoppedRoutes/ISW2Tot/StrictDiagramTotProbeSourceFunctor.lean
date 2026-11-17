module
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotProbeCoefficientsComparison
public import SerrePositivity.EInfinity.BarrattEccles.FramedLimitProbeFunctor
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.RightFrameHomBifunctor

/-!
状態：D81により停止したBE模型のIS-W2 Tot経路。既存の到達点の保管用。
概要：元のprobeつきright frame Homと重み付きHomの係数を、始域全体で同じ全関手にする。
方針：既存のprobe関手・coyonedaの前合成と、元の反対射の同型を全始域で束ねる。
規約：IS-W2 R02〜R03の既存構成の係数移送・始域作用の表示。元のprobe・frameは同じ。
使われ方：固定した始域ごとの比較を、始域にも自然な比較へ結ぶ際の元の構造射。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
open _root_.CategoryTheory _root_.HomotopicalAlgebra _root_.SSet
open _root_.SerrePositivity.DiagramModel
open _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]
local instance strictBETotProbeSourceFunctorModel : ModelCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra := _root_.SerrePositivity.EInfinity.BarrattEccles.modelCategory A

/-- 元のprobeつき実right frame Homを、始域と全標的の二変数で読む。 -/
def strictBETotProbeRightHomBifunctor :
    (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebraᵒᵖ ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra ⥤ SSet.{u} :=
  (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbeFunctor A).op ⋙ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHomBifunctor (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A)

/-- 元の全図式Fに沿い、同じ始域全体のraw Hom係数を束ねる。 -/
def strictBETotProbeRightHomSourceFunctor (F : K ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebraᵒᵖ ⥤ Kᵒᵖᵒᵖ ⥤ SSet.{u} :=
  _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeRightHomBifunctor A ⋙
    (Functor.whiskeringLeft Kᵒᵖᵒᵖ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra SSet.{u}).obj
      ((opOpEquivalence K).functor ⋙ F)

/-- 同じ全始域関手の値は、元の同じraw係数図式。 -/
theorem strictBETotProbeRightHomSourceFunctor_obj (F : K ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra)
    (Y : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeRightHomSourceFunctor A K F).obj (Opposite.op Y) =
      _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeRightHomDiagram A K F Y := rfl

/-- 元のweighted Homの係数も、同じprobe関手により全始域で束ねる。 -/
def strictBETotProbeCoefficientsSourceFunctor (F : K ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebraᵒᵖ ⥤ Kᵒᵖᵒᵖ ⥤ SSet.{u} :=
  (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbeFunctor A).op ⋙ FrameWeightRealization.hom Kᵒᵖ (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameDiagram A K F)

/-- 元の反対射の同型は、全始域についても同じ自然同型。 -/
def strictBETotProbeCoefficientsSourceIso (F : K ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeRightHomSourceFunctor A K F ≅ _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeCoefficientsSourceFunctor A K F :=
  NatIso.ofComponents (fun Y => _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeCoefficientsIso A K F Y.unop) (by
    intro Y Z f
    apply NatTrans.ext
    funext i
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro g
    rfl)

end SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
