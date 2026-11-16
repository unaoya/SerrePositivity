module
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotJointHomInput
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.RightMixedBifunctor

/-!
状態：D81により停止したBE模型のIS-W2 Tot経路。既存の到達点の保管用。
概要：元の六辺のHom比較の最初の三辺を、同じ両変数の全図式としてまとめる。
方針：既存の関手的source frame・混合比較・標的置換をそのままuncurryする。
規約：IS-W2 R02〜R03の自然性・係数移送則。最後のroofと正本Hom∞への比較は含めない。
使われ方：全joint比較の最初の三辺で、元の比較射と弱同値性を保持する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
open _root_.CategoryTheory _root_.HomotopicalAlgebra _root_.SSet
open _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
variable (A : Type u) [CommRing A]
local instance jointFirstSpanModel : ModelCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra := _root_.SerrePositivity.EInfinity.BarrattEccles.modelCategory A
local instance jointFirstSpanFactorization :
    (cofibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) := ⟨⟨_root_.SerrePositivity.EInfinity.BarrattEccles.mappingCofibrantFactorization A⟩⟩
local instance jointFirstSpanCof (X : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    IsCofibrant (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe A X) := _root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe_cofibrant A X

/-- 同じ四つのraw図式を、始域についても反変な関手にする。 -/
def strictBETotJointFirstSpanBifunctor :
    Fin 4 → ((_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebraᵒᵖ ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra ⥤ SSet.{u}) := fun
  | 0 => _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeRightHomBifunctor A
  | 1 => _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeRightHomBifunctor A ⋙
      (Functor.whiskeringLeft (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra SSet.{u}).obj
        (rightFrameReplacement (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A))
  | 2 => (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbeFunctor A).op ⋙
      _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightMixedBifunctor
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelSourceFrameFamily (C := (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra))
        (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A) ⋙
      (Functor.whiskeringLeft (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra SSet.{u}).obj
        (rightFrameReplacement (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A))
  | 3 => (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbeFunctor A).op ⋙
      _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.sourceFrameHomBifunctor
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelSourceFrameFamily (C := (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra)) ⋙
      (Functor.whiskeringLeft (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra SSet.{u}).obj
        (rightFrameReplacement (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A))

/-- 元の標的置換単位は、始域方向にも自然な同じ第一辺。 -/
def strictBETotJointFirstSpanUnit :
    _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointFirstSpanBifunctor A 0 ⟶ _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointFirstSpanBifunctor A 1 where
  app X := Functor.whiskerRight (rightFrameReplacementUnit (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A))
    (rightFrameHom (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A) (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe A X.unop))
  naturality X Y f := by
    ext Z n h
    change (((_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbeFunctor A).map f.unop) ≫ h) ≫
        (((SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameDiagram (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A)).map
          ((rightFrameReplacementUnit (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A)).app Z)).app n) =
      ((_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbeFunctor A).map f.unop) ≫
        (h ≫ (((SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameDiagram (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A)).map
          ((rightFrameReplacementUnit (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A)).app Z)).app n))
    exact Category.assoc _ _ _

/-- 同じ混合右比較を両変数で束ねた第二辺。 -/
def strictBETotJointFirstSpanRight :
    _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointFirstSpanBifunctor A 1 ⟶ _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointFirstSpanBifunctor A 2 :=
  Functor.whiskerRight
    (Functor.whiskerLeft (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbeFunctor A).op
      (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightMixedRightBifunctorMap
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelSourceFrameFamily (C := (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra))
        (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A)))
    ((Functor.whiskeringLeft (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra SSet.{u}).obj
      (rightFrameReplacement (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A)))

/-- 同じ混合左比較を両変数で束ねた逆向きの第三辺。 -/
def strictBETotJointFirstSpanLeft :
    _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointFirstSpanBifunctor A 3 ⟶ _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointFirstSpanBifunctor A 2 :=
  Functor.whiskerRight
    (Functor.whiskerLeft (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbeFunctor A).op
      (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightMixedLeftBifunctorMap
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelSourceFrameFamily (C := (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra))
        (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A)))
    ((Functor.whiskeringLeft (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra SSet.{u}).obj
      (rightFrameReplacement (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A)))

/-- 両変数の積で同じ四つの係数を同じ宇宙へ持ち上げる。 -/
def strictBETotJointFirstSpanDiagram (i : Fin 4) :
    ((_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebraᵒᵖ × (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) ⥤ SSet.{u+1} :=
  Functor.uncurry.obj (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointFirstSpanBifunctor A i) ⋙ SSet.uliftFunctor.{u+1,u}

/-- 元の三辺の始域添字。 -/
def strictBETotJointFirstSpanEdgeSource : Fin 3 → Fin 4 := fun
  | 0 => 0 | 1 => 1 | 2 => 3

/-- 元の三辺の終域添字。 -/
def strictBETotJointFirstSpanEdgeTarget : Fin 3 → Fin 4 := fun
  | 0 => 1 | 1 => 2 | 2 => 2

/-- 同じ三辺をuncurryし、全係数に同じ宇宙変更を施す。 -/
def strictBETotJointFirstSpanEdge (i : Fin 3) :
    _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointFirstSpanDiagram A (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointFirstSpanEdgeSource i) ⟶
      _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointFirstSpanDiagram A (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointFirstSpanEdgeTarget i) :=
  match i with
  | 0 => Functor.whiskerRight (Functor.uncurry.map (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointFirstSpanUnit A)) _
  | 1 => Functor.whiskerRight (Functor.uncurry.map (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointFirstSpanRight A)) _
  | 2 => Functor.whiskerRight (Functor.uncurry.map (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointFirstSpanLeft A)) _

/-- 同じ三辺の全成分は、元の固定始域比較と同じ弱同値。 -/
theorem strictBETotJointFirstSpanEdge_weak (i : Fin 3)
    (P : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebraᵒᵖ × (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    IsWeakHomotopyEquivalence ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointFirstSpanEdge A i).app P) := by
  fin_cases i
  · exact _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockFamilyEdge_weak
      ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelSourceFrameFamily (C := (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra)).atObject
        (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe A P.1.unop)) (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A) (_root_.SerrePositivity.EInfinity.BarrattEccles.mappingCofibrantFactorization A) 0 P.2
  · exact _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockFamilyEdge_weak
      ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelSourceFrameFamily (C := (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra)).atObject
        (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe A P.1.unop)) (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A) (_root_.SerrePositivity.EInfinity.BarrattEccles.mappingCofibrantFactorization A) 1 P.2
  · exact _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockFamilyEdge_weak
      ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelSourceFrameFamily (C := (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra)).atObject
        (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe A P.1.unop)) (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A) (_root_.SerrePositivity.EInfinity.BarrattEccles.mappingCofibrantFactorization A) 2 P.2

/-- 同じ両変数の各係数図式を、同じEx∞によってKan図式にする。 -/
def strictBETotJointFirstSpanKanDiagram (i : Fin 4) :
    _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomIndex A ⥤ KanObject.{u+1} :=
  AsSmall.down ⋙ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.kanHomFamily (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointFirstSpanDiagram A i)

/-- 三辺自身のKan化。 -/
def strictBETotJointFirstSpanKanEdge (i : Fin 3) :
    _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointFirstSpanKanDiagram A (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointFirstSpanEdgeSource i) ⋙ kanObjectForget ⟶
      _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointFirstSpanKanDiagram A (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointFirstSpanEdgeTarget i) ⋙ kanObjectForget :=
  Functor.whiskerLeft AsSmall.down (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.kanHomFamilyMap (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointFirstSpanEdge A i))

/-- 同じ両変数の四つのcoherentな入力。 -/
def strictBETotJointFirstSpanCoherent (i : Fin 4) :
    (SSet.uliftFunctor.{u+2,u+1}).obj (nerve (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomIndex A)) ⟶ SpaceInfinity.{u+1} :=
  kanDiagramCoherentNerve (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointFirstSpanKanDiagram A i)

/-- 同じ実三辺は両変数の全関手圏でも可逆。 -/
def strictBETotJointFirstSpanEdgeIso (i : Fin 3) :
    FunctorIso (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointFirstSpanCoherent A (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointFirstSpanEdgeSource i))
      (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointFirstSpanCoherent A (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointFirstSpanEdgeTarget i)) :=
  kanDiagramFunctorIsoOfPointwise
    (F := ⟨_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointFirstSpanKanDiagram A (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointFirstSpanEdgeSource i), trivial⟩)
    (G := ⟨_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointFirstSpanKanDiagram A (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointFirstSpanEdgeTarget i), trivial⟩)
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointFirstSpanKanEdge A i)
    (fun P => _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.kanHomFamilyMap_isQCatEquivalence _
      (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointFirstSpanEdge_weak A i) (AsSmall.down.obj P))

/-- 元の第一入力は、すでに構成した両変数raw Homの全入力そのもの。 -/
theorem strictBETotJointFirstSpanCoherent_zero :
    _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointFirstSpanCoherent A 0 = _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointRawHomCoherent A := rfl

/-- 最初の三辺を合成した、元の両変数raw Homとsource frame Homの全関手同型。 -/
def strictBETotJointFirstSpanComparison :
    FunctorIso (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointRawHomCoherent A) (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointFirstSpanCoherent A 3) :=
  (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointFirstSpanEdgeIso A 0).trans
    ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointFirstSpanEdgeIso A 1).trans (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointFirstSpanEdgeIso A 2).symm)

end SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
