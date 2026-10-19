module
public import SerrePositivity.KST.SConstruction.PointedKanDiagramEquivalences
public import SerrePositivity.KST.SConstruction.OneDirectionWeakComparison

/-! # 一方向比較の図式全体の coherent な逆
概要：一方向 Kan 模型から境界 Kan 模型への元の自然比較を図式全体で反転する。
方針：元の全基点 π_* 同型を点つき Kan 値の関手 ∞ 圏の同型へ移す。
規約：小さい通常の入力図式 I に対し、逆辺は ULift N(I) の全単体を同時に持つ。
使われ方：構造射の逆射側の全射列の整合性。元の選択逆射との照合は別に行う。
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

/-- 一方向模型を元の射のまま点つき Kan 対象の図式にする。 -/
def oneDirectionPointedKanDiagram {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) : I ⥤ PointedKanObject.{u} :=
  pointedKanDiagram (F ⋙ oneDirectionKanRealizationFunctor r)
    (fun i => oneDirectionKanRealization_kanComplex r (F.obj i))

/-- 境界模型を元の射のまま点つき Kan 対象の図式にする。 -/
def boundaryPointedKanDiagram {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) : I ⥤ PointedKanObject.{u} :=
  pointedKanDiagram (F ⋙ boundaryKanRealizationFunctor r)
    (fun i => boundaryKanRealization_kanComplex r (F.obj i))

/-- 元の一方向比較の自然変換を図式全体の coherent な関手同型にする。 -/
def oneDirectionCoherentComparisonIso {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) :=
  pointedKanDiagramFunctorIso
    (fun i => oneDirectionKanRealization_kanComplex r (F.obj i))
    (fun i => boundaryKanRealization_kanComplex r (F.obj i))
    (Functor.whiskerLeft F (oneDirectionKanComparisonNat r))
    (fun i => oneDirectionReducedComparison_kan_piIsomorphism r (F.obj i))

/-- 全入力射列に同時に自然な、一方向比較の図式全体の逆の円柱。 -/
def oneDirectionCoherentInverseHomotopy {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) :=
  pointedKanDiagramInverseHomotopy
    (fun i => oneDirectionKanRealization_kanComplex r (F.obj i))
    (fun i => boundaryKanRealization_kanComplex r (F.obj i))
    (Functor.whiskerLeft F (oneDirectionKanComparisonNat r))
    (fun i => oneDirectionReducedComparison_kan_piIsomorphism r (F.obj i))

end SerrePositivity.KST.SConstruction
