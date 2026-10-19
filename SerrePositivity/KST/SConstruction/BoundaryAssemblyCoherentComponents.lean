module
public import SerrePositivity.KST.SConstruction.BoundaryAssemblyCoherentDiagram
public import SerrePositivity.KST.SConstruction.PointedKanHomotopyComponents

/-! # 全射列に自然な組み立ての元の Kan 模型上の成分
概要：図式全体で選んだ比較逆射・延長・組み立てから実際の点つき成分を取り出す。
方針：coherent nerve の辺を元の Kan 対象間の通常の射へ厳密に戻す。
規約：両端は既存の境界・一方向・loop 模型そのもの。既存の選択構造射との成分照合は別工程。
使われ方：全射列の変換を元の BF K の構造射へ接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open scoped Simplicial

/-- 比較の coherent な全体逆から回収した、元の Kan 模型間の点つき逆射。 -/
def oneDirectionCoherentInverseDiagramMapAt {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) (i : I) :
    (boundaryKanRealizationFunctor r).obj (F.obj i) ⟶
      (oneDirectionKanRealizationFunctor r).obj (F.obj i) :=
  pointedKanDiagramHomotopyMapAt
    (fun i => boundaryKanRealization_kanComplex r (F.obj i))
    (fun i => oneDirectionKanRealization_kanComplex r (F.obj i))
    (oneDirectionCoherentInverseHomotopy r F) i

/-- coherent な全体延長から回収した、元の一方向 Kan 模型から loop への点つき射。 -/
def kanAssemblyCoherentDiagramMapAt {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) (i : I) :
    (oneDirectionKanRealizationFunctor r).obj (F.obj i) ⟶
      (loopBoundaryKanFunctor (r + 1)).obj (F.obj i) :=
  pointedKanDiagramHomotopyMapAt
    (fun i => oneDirectionKanRealization_kanComplex r (F.obj i))
    (fun i => loopBoundaryKan_kanComplex (r + 1) (F.obj i))
    (kanAssemblyCoherentDiagramHomotopy r F) i

/-- 全射列にわたる組み立て変換の、元の境界 Kan 模型上の実際の点つき成分。 -/
def boundaryAssemblyCoherentDiagramMapAt {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) (i : I) :
    (boundaryKanRealizationFunctor r).obj (F.obj i) ⟶
      (loopBoundaryKanFunctor (r + 1)).obj (F.obj i) :=
  pointedKanDiagramHomotopyMapAt
    (fun i => boundaryKanRealization_kanComplex r (F.obj i))
    (fun i => loopBoundaryKan_kanComplex (r + 1) (F.obj i))
    (boundaryAssemblyCoherentDiagramHomotopy r F) i

end SerrePositivity.KST.SConstruction
