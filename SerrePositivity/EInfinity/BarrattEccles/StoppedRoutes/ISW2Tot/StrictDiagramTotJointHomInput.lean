module
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotProbeSourceFunctor
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotFrameHomInfinity
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.NerveOpposite
public import Mathlib.CategoryTheory.Functor.Currying

/-!
状態：D81により停止したBE模型のIS-W2 Tot経路。既存の到達点の保管用。
概要：元の両変数raw Homと正本Hom∞の全比較の二つの入力を、同じ底・宇宙に揃える。
方針：元のuncurry・AsSmall・ULift・Ex∞と、同じCAlg源の二つの射影を合成する。
規約：IS-W2 R02〜R03の既存図式の全係数表示。二入力間の全同型はここでは主張しない。
使われ方：固定始域ごとの比較と両変数のcoherentな比較を型で区別する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
open _root_.CategoryTheory _root_.HomotopicalAlgebra _root_.SSet _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A]
local instance strictBETotJointHomInputModel : ModelCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra := _root_.SerrePositivity.EInfinity.BarrattEccles.modelCategory A

local instance strictBETotJointHomInputFactorization :
    (cofibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) := ⟨⟨_root_.SerrePositivity.EInfinity.BarrattEccles.mappingCofibrantFactorization A⟩⟩
local instance strictBETotJointHomInputCof (X : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    IsCofibrant (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe A X) := _root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe_cofibrant A X

/-- 元の両変数の圏を同じ大きい通常の添字にする。 -/
abbrev strictBETotJointHomIndex :=
  AsSmall.{u+1} ((_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebraᵒᵖ × (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra)

/-- 元のprobeつきraw Homを、同じ二変数の積でuncurryする。 -/
def strictBETotJointRawHom :
    ((_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebraᵒᵖ × (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) ⥤ SSet.{u} :=
  Functor.uncurry.obj (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeRightHomBifunctor A)

/-- 元の両変数raw Homを、同じ係数の宇宙変更とEx∞に送る全Kan図式。 -/
def strictBETotJointRawHomKan : _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomIndex A ⥤ KanObject.{u+1} :=
  AsSmall.down ⋙ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.kanHomFamily (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointRawHom A ⋙ SSet.uliftFunctor.{u+1,u})

/-- 両変数raw Homの同じcoherentな実現。 -/
def strictBETotJointRawHomCoherent :
    (SSet.uliftFunctor.{u+2,u+1}).obj (nerve (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomIndex A)) ⟶ SpaceInfinity.{u+1} :=
  kanDiagramCoherentNerve (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointRawHomKan A)

/-- 同じ積添字の第一射影を、同じモデル源の反対添字にする。 -/
def strictBETotJointHomSourceIndex :
    _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomIndex A ⥤ (AsSmall.{u+1} (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra)ᵒᵖ :=
  AsSmall.down ⋙ CategoryTheory.Prod.fst (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebraᵒᵖ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra ⋙
    (AsSmall.up : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra ⥤ AsSmall.{u+1} (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).op

/-- 同じ積添字の第二射影を、同じモデル源の添字にする。 -/
def strictBETotJointHomTargetIndex :
    _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomIndex A ⥤ AsSmall.{u+1} (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra :=
  AsSmall.down ⋙ CategoryTheory.Prod.snd (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebraᵒᵖ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra ⋙ AsSmall.up

/-- 同じ元のCAlg源の両変数を組にした、正本Hom∞の底への指定射。 -/
def strictBETotJointNativeHomInput :
    nerve (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomIndex A) ⟶ (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A).op ⊗ _root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A :=
  CartesianMonoidalCategory.lift
    (nerveMap (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomSourceIndex A) ≫
      (nerveOppositeIso (C := AsSmall.{u+1} (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra)).inv ≫
        SSet.opFunctor.map (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A))
    (nerveMap (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomTargetIndex A) ≫ _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A)

/-- 同じCAlg源の正本の二変数Hom∞を、上の同じ元の底へ引き戻す。 -/
def strictBETotJointNativeHomCoherent :
    (SSet.uliftFunctor.{u+2,u+1}).obj (nerve (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomIndex A)) ⟶ SpaceInfinity.{u+1} :=
  (SSet.uliftFunctor.{u+2,u+1}).map (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointNativeHomInput A) ≫
    twistedArrowHomInfinity (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A)

/-- 元の始域を固定する、同じ大きい通常の添字の包含。 -/
def strictBETotJointHomFixSource (X : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    AsSmall.{u+1} (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra ⥤ _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomIndex A :=
  AsSmall.down ⋙ CategoryTheory.Prod.sectR (Opposite.op X) (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra ⋙ AsSmall.up

/-- uncurryの始域を固定すると、元の同じ実right frame Homに戻る。 -/
theorem strictBETotJointRawHom_fixSource (X : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    CategoryTheory.Prod.sectR (Opposite.op X) (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra ⋙ _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointRawHom A =
      rightFrameHom (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A) (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe A X) := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro Y Z f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change (((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeRightHomBifunctor A).map (𝟙 (Opposite.op X))).app Y) ≫
    ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeRightHomBifunctor A).obj (Opposite.op X)).map f =
      ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeRightHomBifunctor A).obj (Opposite.op X)).map f
  rw [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]

/-- 同じ全Kan入力の始域制限は、既存の全frame比較の第零図式そのもの。 -/
theorem strictBETotJointRawHomKan_fixSource (X : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomFixSource A X ⋙ _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointRawHomKan A =
      _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockKanDiagram
        ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelSourceFrameFamily (C := (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra)).atObject
          (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe A X)) (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A) 0 := by
  change AsSmall.down ⋙ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.kanHomFamily
      ((CategoryTheory.Prod.sectR (Opposite.op X) (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra ⋙
        _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointRawHom A) ⋙ SSet.uliftFunctor.{u+1,u}) =
    AsSmall.down ⋙ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.kanHomFamily
      (rightFrameHom (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A) (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe A X) ⋙ SSet.uliftFunctor.{u+1,u})
  rw [_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointRawHom_fixSource]

/-- 同じcoherent入力の始域制限も、既存の第零全比較のcoherentな入力に厳密に等しい。 -/
theorem strictBETotJointRawHomCoherent_fixSource (X : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    (SSet.uliftFunctor.{u+2,u+1}).map (nerveMap (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomFixSource A X)) ≫
      _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointRawHomCoherent A =
    _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockCoherentDiagram
      ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelSourceFrameFamily (C := (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra)).atObject
        (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe A X)) (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A) 0 := by
  change _ ≫ kanDiagramCoherentNerve (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointRawHomKan A) = _
  rw [kanDiagramCoherentNerve_precomp, _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointRawHomKan_fixSource]
  rfl

end SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
