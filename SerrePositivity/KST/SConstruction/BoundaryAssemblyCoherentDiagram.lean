module
public import SerrePositivity.KST.SConstruction.OneDirectionCoherentInverseDiagram
public import SerrePositivity.KST.SConstruction.PointedKanDiagramExtensions
public import SerrePositivity.KST.SConstruction.KanAssemblyAdjoint

/-! # 元の境界模型間の全入力射列に自然な組み立て変換
概要：境界 Kan 模型から次段の loop への変換を入力図式の全単体で同時に構成する。
方針：一方向比較の図式全体の逆と、随伴射の coherent な Kan 延長を合成する。
規約：小さい通常の入力図式に対するもの。既存の選択構造射との点つき成分の照合は別工程。
使われ方：元の BF K スペクトルの構造射の coherent な自然性への接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open Spectra
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 元の随伴射を、一方向 Kan 模型から loop への図式全体の変換へ延長する。 -/
def kanAssemblyCoherentDiagramHomotopy {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) :=
  pointedKanDiagramExtensionHomotopy (fun i => loopBoundaryKan_kanComplex (r + 1) (F.obj i))
    (Functor.whiskerLeft F (kanTargetAssemblyAdjointNat r))

/-- 延長の実際の二つの因子と、図式全体の延長を結ぶ実三角形。 -/
def kanAssemblyCoherentDiagramTriangle {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) :=
  pointedKanDiagramExtensionTriangle (fun i => loopBoundaryKan_kanComplex (r + 1) (F.obj i))
    (Functor.whiskerLeft F (kanTargetAssemblyAdjointNat r))

/-- 元の境界 Kan 模型から次段の loop への、全射列を同時に持つ coherent な変換。 -/
def boundaryAssemblyCoherentDiagramHomotopy {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) :
    SSet.Homotopy
      (pointedKanCoherentDiagram (F ⋙ boundaryKanRealizationFunctor r)
        (fun i => boundaryKanRealization_kanComplex r (F.obj i)))
      (pointedKanCoherentDiagram (F ⋙ loopBoundaryKanFunctor (r + 1))
        (fun i => loopBoundaryKan_kanComplex (r + 1) (F.obj i))) :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomotopyComposite (oneDirectionCoherentInverseHomotopy r F)
    (kanAssemblyCoherentDiagramHomotopy r F)

/-- 図式全体の組み立ては、元の二つの coherent な因子と実三角形をなす。 -/
def boundaryAssemblyCoherentDiagramTriangle {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle (oneDirectionCoherentInverseHomotopy r F)
      (kanAssemblyCoherentDiagramHomotopy r F) (boundaryAssemblyCoherentDiagramHomotopy r F) :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomotopyCompositeTriangle _ _

end SerrePositivity.KST.SConstruction
