module
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointHomInput
public import SerrePositivity.EInfinity.FrameHom.RightMixedBifunctor

/-!
概要：元の六辺のHom比較の最初の三辺を、同じ両変数の全図式としてまとめる。
方針：既存の関手的source frame・混合比較・標的置換をそのままuncurryする。
規約：IS-W2 R02〜R03の自然性・係数移送則。最後のroofと正本Hom∞への比較は含めない。
使われ方：全joint比較の最初の三辺で、元の比較射と弱同値性を保持する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory HomotopicalAlgebra SSet
open SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
variable (A : Type u) [CommRing A]
local instance jointFirstSpanModel : ModelCategory (operad A).Algebra := modelCategory A
local instance jointFirstSpanFactorization :
    (cofibrations (operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (operad A).Algebra) := ⟨⟨mappingCofibrantFactorization A⟩⟩
local instance jointFirstSpanCof (X : (operad A).Algebra) :
    IsCofibrant (framedLimitProbe A X) := framedLimitProbe_cofibrant A X

/-- 同じ四つのraw図式を、始域についても反変な関手にする。 -/
def strictBETotJointFirstSpanBifunctor :
    Fin 4 → ((operad A).Algebraᵒᵖ ⥤ (operad A).Algebra ⥤ SSet.{u}) := fun
  | 0 => strictBETotProbeRightHomBifunctor A
  | 1 => strictBETotProbeRightHomBifunctor A ⋙
      (Functor.whiskeringLeft (operad A).Algebra (operad A).Algebra SSet.{u}).obj
        (rightFrameReplacement (rightFrameFamily A))
  | 2 => (framedLimitProbeFunctor A).op ⋙
      FrameHom.rightMixedBifunctor
        (SimplicialLocalization.modelSourceFrameFamily (C := (operad A).Algebra))
        (rightFrameFamily A) ⋙
      (Functor.whiskeringLeft (operad A).Algebra (operad A).Algebra SSet.{u}).obj
        (rightFrameReplacement (rightFrameFamily A))
  | 3 => (framedLimitProbeFunctor A).op ⋙
      FrameHom.sourceFrameHomBifunctor
        (SimplicialLocalization.modelSourceFrameFamily (C := (operad A).Algebra)) ⋙
      (Functor.whiskeringLeft (operad A).Algebra (operad A).Algebra SSet.{u}).obj
        (rightFrameReplacement (rightFrameFamily A))

/-- 元の標的置換単位は、始域方向にも自然な同じ第一辺。 -/
def strictBETotJointFirstSpanUnit :
    strictBETotJointFirstSpanBifunctor A 0 ⟶ strictBETotJointFirstSpanBifunctor A 1 where
  app X := Functor.whiskerRight (rightFrameReplacementUnit (rightFrameFamily A))
    (rightFrameHom (rightFrameFamily A) (framedLimitProbe A X.unop))
  naturality X Y f := by
    ext Z n h
    change (((framedLimitProbeFunctor A).map f.unop) ≫ h) ≫
        (((SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameDiagram (rightFrameFamily A)).map
          ((rightFrameReplacementUnit (rightFrameFamily A)).app Z)).app n) =
      ((framedLimitProbeFunctor A).map f.unop) ≫
        (h ≫ (((SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameDiagram (rightFrameFamily A)).map
          ((rightFrameReplacementUnit (rightFrameFamily A)).app Z)).app n))
    exact Category.assoc _ _ _

/-- 同じ混合右比較を両変数で束ねた第二辺。 -/
def strictBETotJointFirstSpanRight :
    strictBETotJointFirstSpanBifunctor A 1 ⟶ strictBETotJointFirstSpanBifunctor A 2 :=
  Functor.whiskerRight
    (Functor.whiskerLeft (framedLimitProbeFunctor A).op
      (FrameHom.rightMixedRightBifunctorMap
        (SimplicialLocalization.modelSourceFrameFamily (C := (operad A).Algebra))
        (rightFrameFamily A)))
    ((Functor.whiskeringLeft (operad A).Algebra (operad A).Algebra SSet.{u}).obj
      (rightFrameReplacement (rightFrameFamily A)))

/-- 同じ混合左比較を両変数で束ねた逆向きの第三辺。 -/
def strictBETotJointFirstSpanLeft :
    strictBETotJointFirstSpanBifunctor A 3 ⟶ strictBETotJointFirstSpanBifunctor A 2 :=
  Functor.whiskerRight
    (Functor.whiskerLeft (framedLimitProbeFunctor A).op
      (FrameHom.rightMixedLeftBifunctorMap
        (SimplicialLocalization.modelSourceFrameFamily (C := (operad A).Algebra))
        (rightFrameFamily A)))
    ((Functor.whiskeringLeft (operad A).Algebra (operad A).Algebra SSet.{u}).obj
      (rightFrameReplacement (rightFrameFamily A)))

/-- 両変数の積で同じ四つの係数を同じ宇宙へ持ち上げる。 -/
def strictBETotJointFirstSpanDiagram (i : Fin 4) :
    ((operad A).Algebraᵒᵖ × (operad A).Algebra) ⥤ SSet.{u+1} :=
  Functor.uncurry.obj (strictBETotJointFirstSpanBifunctor A i) ⋙ SSet.uliftFunctor.{u+1,u}

/-- 元の三辺の始域添字。 -/
def strictBETotJointFirstSpanEdgeSource : Fin 3 → Fin 4 := fun
  | 0 => 0 | 1 => 1 | 2 => 3

/-- 元の三辺の終域添字。 -/
def strictBETotJointFirstSpanEdgeTarget : Fin 3 → Fin 4 := fun
  | 0 => 1 | 1 => 2 | 2 => 2

/-- 同じ三辺をuncurryし、全係数に同じ宇宙変更を施す。 -/
def strictBETotJointFirstSpanEdge (i : Fin 3) :
    strictBETotJointFirstSpanDiagram A (strictBETotJointFirstSpanEdgeSource i) ⟶
      strictBETotJointFirstSpanDiagram A (strictBETotJointFirstSpanEdgeTarget i) :=
  match i with
  | 0 => Functor.whiskerRight (Functor.uncurry.map (strictBETotJointFirstSpanUnit A)) _
  | 1 => Functor.whiskerRight (Functor.uncurry.map (strictBETotJointFirstSpanRight A)) _
  | 2 => Functor.whiskerRight (Functor.uncurry.map (strictBETotJointFirstSpanLeft A)) _

/-- 同じ三辺の全成分は、元の固定始域比較と同じ弱同値。 -/
theorem strictBETotJointFirstSpanEdge_weak (i : Fin 3)
    (P : (operad A).Algebraᵒᵖ × (operad A).Algebra) :
    IsWeakHomotopyEquivalence ((strictBETotJointFirstSpanEdge A i).app P) := by
  fin_cases i
  · exact FrameHom.rightFrameHammockFamilyEdge_weak
      ((SimplicialLocalization.modelSourceFrameFamily (C := (operad A).Algebra)).atObject
        (framedLimitProbe A P.1.unop)) (rightFrameFamily A) (mappingCofibrantFactorization A) 0 P.2
  · exact FrameHom.rightFrameHammockFamilyEdge_weak
      ((SimplicialLocalization.modelSourceFrameFamily (C := (operad A).Algebra)).atObject
        (framedLimitProbe A P.1.unop)) (rightFrameFamily A) (mappingCofibrantFactorization A) 1 P.2
  · exact FrameHom.rightFrameHammockFamilyEdge_weak
      ((SimplicialLocalization.modelSourceFrameFamily (C := (operad A).Algebra)).atObject
        (framedLimitProbe A P.1.unop)) (rightFrameFamily A) (mappingCofibrantFactorization A) 2 P.2

/-- 同じ両変数の各係数図式を、同じEx∞によってKan図式にする。 -/
def strictBETotJointFirstSpanKanDiagram (i : Fin 4) :
    strictBETotJointHomIndex A ⥤ KanObject.{u+1} :=
  AsSmall.down ⋙ FrameHom.kanHomFamily (strictBETotJointFirstSpanDiagram A i)

/-- 三辺自身のKan化。 -/
def strictBETotJointFirstSpanKanEdge (i : Fin 3) :
    strictBETotJointFirstSpanKanDiagram A (strictBETotJointFirstSpanEdgeSource i) ⋙ kanObjectForget ⟶
      strictBETotJointFirstSpanKanDiagram A (strictBETotJointFirstSpanEdgeTarget i) ⋙ kanObjectForget :=
  Functor.whiskerLeft AsSmall.down (FrameHom.kanHomFamilyMap (strictBETotJointFirstSpanEdge A i))

/-- 同じ両変数の四つのcoherentな入力。 -/
def strictBETotJointFirstSpanCoherent (i : Fin 4) :
    (SSet.uliftFunctor.{u+2,u+1}).obj (nerve (strictBETotJointHomIndex A)) ⟶ SpaceInfinity.{u+1} :=
  kanDiagramCoherentNerve (strictBETotJointFirstSpanKanDiagram A i)

/-- 同じ実三辺は両変数の全関手圏でも可逆。 -/
def strictBETotJointFirstSpanEdgeIso (i : Fin 3) :
    FunctorIso (strictBETotJointFirstSpanCoherent A (strictBETotJointFirstSpanEdgeSource i))
      (strictBETotJointFirstSpanCoherent A (strictBETotJointFirstSpanEdgeTarget i)) :=
  kanDiagramFunctorIsoOfPointwise
    (F := ⟨strictBETotJointFirstSpanKanDiagram A (strictBETotJointFirstSpanEdgeSource i), trivial⟩)
    (G := ⟨strictBETotJointFirstSpanKanDiagram A (strictBETotJointFirstSpanEdgeTarget i), trivial⟩)
    (strictBETotJointFirstSpanKanEdge A i)
    (fun P => FrameHom.kanHomFamilyMap_isQCatEquivalence _
      (strictBETotJointFirstSpanEdge_weak A i) (AsSmall.down.obj P))

/-- 元の第一入力は、すでに構成した両変数raw Homの全入力そのもの。 -/
theorem strictBETotJointFirstSpanCoherent_zero :
    strictBETotJointFirstSpanCoherent A 0 = strictBETotJointRawHomCoherent A := rfl

/-- 最初の三辺を合成した、元の両変数raw Homとsource frame Homの全関手同型。 -/
def strictBETotJointFirstSpanComparison :
    FunctorIso (strictBETotJointRawHomCoherent A) (strictBETotJointFirstSpanCoherent A 3) :=
  (strictBETotJointFirstSpanEdgeIso A 0).trans
    ((strictBETotJointFirstSpanEdgeIso A 1).trans (strictBETotJointFirstSpanEdgeIso A 2).symm)

end SerrePositivity.EInfinity.BarrattEccles
