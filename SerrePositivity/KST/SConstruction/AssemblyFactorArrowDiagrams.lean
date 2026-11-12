module
public import SerrePositivity.KST.SConstruction.PointedExtensionArrowDiagram
public import SerrePositivity.KST.SConstruction.PointedLiftArrowDiagram
public import SerrePositivity.KST.SConstruction.KanAssemblyMixedChoices
public import SerrePositivity.KST.SConstruction.OneDirectionInverseMixedChoices

/-! # 構造射の両因子の全入力射にわたる図式
概要：任意の入力図式に沿う Kan 延長・比較逆射の混合空間を厳密な関手へ束ねる。
方針：元の Kan 単位と mapping path 射影の自然変換を使う。
規約：各成分は元の混合選択空間そのもので、余分な選択を加えない。
使われ方：全ての入力射列にわたる因子の coherent な選択。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open Spectra
open SerrePositivity.InfinityCategories

/-- 一方向実現の源を Kan 置換する厳密な単位自然変換。 -/
def oneDirectionKanUnitNat (r : ℕ) :
    oneDirectionReducedRealizationFunctor r ⟶ oneDirectionKanRealizationFunctor r :=
  Functor.whiskerLeft (oneDirectionReducedRealizationFunctor r) PointedKanReplacement.unit

/-- 一方向比較の mapping path の底への射影の自然変換。 -/
def oneDirectionMappingPathProjectionNat (r : ℕ) :
    oneDirectionMappingPathFunctor r ⟶ boundaryKanRealizationFunctor r where
  app X := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathProjection ((oneDirectionKanComparisonNat r).app X)
  naturality _ _ f := oneDirectionMappingPathMap_projection r f

/-- 一方向比較の mapping path の一方向模型への射影の自然変換。 -/
def oneDirectionMappingPathRetractionNat (r : ℕ) :
    oneDirectionMappingPathFunctor r ⟶ oneDirectionKanRealizationFunctor r where
  app X := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction ((oneDirectionKanComparisonNat r).app X)
  naturality _ _ f := oneDirectionMappingPathMap_retraction r f

/-- 入力図式の全射と両側合成にわたる Kan 延長の混合選択空間。 -/
def kanAssemblyInputArrowDiagram {I : Type v} [Category.{w} I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) : AssemblyInputArrow I ⥤ SSet.{u} :=
  pointedExtensionArrowDiagram (Functor.whiskerLeft F (oneDirectionKanUnitNat r))
    (Functor.whiskerLeft F (kanTargetAssemblyAdjointNat r))

/-- 入力図式の全射と両側合成にわたる比較逆射の混合選択空間。 -/
def oneDirectionInverseInputArrowDiagram {I : Type v} [Category.{w} I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) : AssemblyInputArrow I ⥤ SSet.{u} :=
  pointedLiftArrowDiagram (Functor.whiskerLeft F (oneDirectionMappingPathProjectionNat r))

/-- 延長図式の各成分は元の入力射の混合延長空間。 -/
lemma kanAssemblyInputArrowDiagram_obj {I : Type v} [Category.{w} I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) (x : AssemblyInputArrow I) :
    (kanAssemblyInputArrowDiagram r F).obj x =
      kanAssemblyMixedChoices r (F.map (assemblyArrowHom x)) := rfl

/-- 逆射図式の各成分は元の入力射の混合持ち上げ空間。 -/
lemma oneDirectionInverseInputArrowDiagram_obj {I : Type v} [Category.{w} I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) (x : AssemblyInputArrow I) :
    (oneDirectionInverseInputArrowDiagram r F).obj x =
      oneDirectionInverseMixedChoices r (F.map (assemblyArrowHom x)) := rfl

/-- 延長図式の全成分は追加仮定なしに可縮 Kan。 -/
lemma kanAssemblyInputArrowDiagram_isContractibleKan {I : Type v} [Category.{w} I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) (x : AssemblyInputArrow I) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan ((kanAssemblyInputArrowDiagram r F).obj x) :=
  kanAssemblyMixedChoices_isContractibleKan r (F.map (assemblyArrowHom x))

/-- 逆射図式の全成分は追加仮定なしに可縮 Kan。 -/
lemma oneDirectionInverseInputArrowDiagram_isContractibleKan {I : Type v} [Category.{w} I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) (x : AssemblyInputArrow I) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan ((oneDirectionInverseInputArrowDiagram r F).obj x) :=
  oneDirectionInverseMixedChoices_isContractibleKan r (F.map (assemblyArrowHom x))

end SerrePositivity.KST.SConstruction
