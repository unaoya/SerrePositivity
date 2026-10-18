module

public import SerrePositivity.InfinityCategories.F1B.TriangleBoundaryPath
public import SerrePositivity.InfinityCategories.F1B.IntervalFamilyPath
public import SerrePositivity.InfinityCategories.F1B.UnitCompositionTriangle

/-!
概要：標準単位比較の像から指定族へのホモトピーを、基準合成三角形の境界の path に組み込む。
方針：二つの合成辺は定値 path で固定し、対角辺に区間族の path を貼る。
規約：与えられたホモトピーを対角辺で厳密に回収する。
使われ方：導来 fiber から逆向きの比較を作る際の相対図式持ち上げへの入力。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：単位比較の像を動かすホモトピーを合成三角形の境界の可逆 path にする。
方針：合成三角形の両端点を確認し、対角辺の path と固定二辺を貼る。
規約：基準三角形は普遍三角形の制限を使い、選び直さない。
使われ方：導来 fiber の path を保持した三角形の輸送。 -/
noncomputable def unitCompositionBoundaryPath {A X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (η : FunctorHom (𝟙 X) (F ≫ G)) (x : X _⦋0⦌) (y : Y _⦋0⦌)
    (f : A ⟶ intervalMappingSpace (F.app (Opposite.op ⦋0⦌) x) y)
    {g : A ⟶ intervalMappingSpace x (G.app (Opposite.op ⦋0⦌) y)}
    (H : SSet.Homotopy (f ≫ unitIntervalMap η x y) g) :
    (boundary 2 : SSet.{u}) ⟶ equivalencePath ((ihom A).obj X) :=
  triangleBoundaryPath (unitIntervalCompositionTriangle_family η x y f).diagram
    (intervalFamilyPath H)
    (by
      simpa only [Category.assoc, reassoc_of% horn.ι_ι,
        reassoc_of% (unitIntervalCompositionTriangle_family η x y f).vertex_zero]
        using intervalFamilyPath_source H)
    (by
      simpa only [Category.assoc, reassoc_of% horn.ι_ι,
        reassoc_of% (unitIntervalCompositionTriangle_family η x y f).vertex_two]
        using intervalFamilyPath_target H)

/-- 概要：基準合成境界の path の対角辺は与えられたホモトピーの path。
方針：境界の第 1 面の制限公式。
規約：実際の path の等式。
使われ方：導来 fiber の path の情報を保つことの検証。 -/
lemma unitCompositionBoundaryPath_diagonal {A X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (η : FunctorHom (𝟙 X) (F ≫ G)) (x : X _⦋0⦌) (y : Y _⦋0⦌)
    (f : A ⟶ intervalMappingSpace (F.app (Opposite.op ⦋0⦌) x) y)
    {g : A ⟶ intervalMappingSpace x (G.app (Opposite.op ⦋0⦌) y)}
    (H : SSet.Homotopy (f ≫ unitIntervalMap η x y) g) :
    boundary.ι (1 : Fin 3) ≫ unitCompositionBoundaryPath η x y f H = intervalFamilyPath H :=
  triangleBoundaryPath_face_one _ _ _ _

/-- 概要：合成境界の path の始点は基準合成三角形の境界。
方針：対角辺の path の始点と基準三角形の第 1 面を照合する。
規約：始点の図式を厳密に指定する。
使われ方：境界の path を持ち上げる際の始点条件。 -/
lemma unitCompositionBoundaryPath_start {A X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (η : FunctorHom (𝟙 X) (F ≫ G)) (x : X _⦋0⦌) (y : Y _⦋0⦌)
    (f : A ⟶ intervalMappingSpace (F.app (Opposite.op ⦋0⦌) x) y)
    {g : A ⟶ intervalMappingSpace x (G.app (Opposite.op ⦋0⦌) y)}
    (H : SSet.Homotopy (f ≫ unitIntervalMap η x y) g) :
    unitCompositionBoundaryPath η x y f H ≫ equivalencePathEndpoint _ 0 =
      (boundary 2).ι ≫ (unitIntervalCompositionTriangle_family η x y f).diagram :=
  triangleBoundaryPath_start _ _ _ _ ((intervalFamilyPath_start H).trans
    (unitIntervalCompositionTriangle_family η x y f).face_one.symm)

end SerrePositivity.InfinityCategories
