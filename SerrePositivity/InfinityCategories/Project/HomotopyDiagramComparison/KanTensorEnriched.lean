module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanTensorAdjunction
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.SimplicialPairNerve
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparisonIso

/-!
概要：Kan 複体の二項積の、両変数に関する単体的 Hom 作用。
方針：二つの評価を同じパラメータで組み、積の対象から curry する。
規約：元の直積と射影を使用。使われ方：点ごとの coherent な空間値積図式。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 二つの Hom の族を、同じパラメータを持つ直積間の射の族へ送る。 -/
def kanTensorHomMap (K L M N : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    (ihom K.obj).obj M.obj ⊗ (ihom L.obj).obj N.obj ⟶
      (ihom (K.obj ⊗ L.obj)).obj (M.obj ⊗ N.obj) :=
  let A := K.obj ⊗ L.obj
  let P := (ihom K.obj).obj M.obj ⊗ (ihom L.obj).obj N.obj
  curry (lift
    (lift (fst A P ≫ fst K.obj L.obj)
      (snd A P ≫ fst _ _) ≫ (ihom.ev K.obj).app M.obj)
    (lift (fst A P ≫ snd K.obj L.obj)
      (snd A P ≫ snd _ _) ≫ (ihom.ev L.obj).app N.obj))

/-- 二項積の同じ Hom 作用は、元の二つの恒等射を直積の恒等射へ送る。 -/
lemma kanTensorHomMap_id (K L : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    lift (eId SSet K) (eId SSet L) ≫ kanTensorHomMap K L K L =
      eId SSet ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanTensorLeft K).obj L) := by
  apply uncurry_injective
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨⟨k, l⟩, t⟩
  apply Prod.ext <;> rfl

/-- Kan 複体の二項直積は、同じ二つの Hom パラメータに作用する豊穣関手。 -/
def kanTensorEnriched :
    EnrichedFunctor SSet.{u} (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.SimplicialPairObject _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} where
  obj X := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanTensorLeft X.1).obj X.2
  map X Y := kanTensorHomMap X.1 X.2 Y.1 Y.2
  map_id X := kanTensorHomMap_id X.1 X.2
  map_comp X Y Z := by
    apply uncurry_injective
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨x, y⟩, ⟨⟨f, g⟩, ⟨h, i⟩⟩⟩
    apply Prod.ext <;> rfl

/-- 第一射影は、全ての高次の Hom の族に対して自然な豊穣比較。 -/
def kanTensorEnrichedFst : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparison kanTensorEnriched
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplicialPairFst _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) := by
  refine ⟨fun X ↦ fst X.1.obj X.2.obj, ?_⟩
  intro X Y
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨⟨x, y⟩, ⟨f, g⟩⟩
  rfl

/-- 第二射影も、同じ全高次の Hom の族に対して自然な豊穣比較。 -/
def kanTensorEnrichedSnd : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparison kanTensorEnriched
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplicialPairSnd _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) := by
  refine ⟨fun X ↦ snd X.1.obj X.2.obj, ?_⟩
  intro X Y
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨⟨x, y⟩, ⟨f, g⟩⟩
  rfl

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
