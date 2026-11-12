module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PointedCoherentFiberComparison
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanTensorEnriched

/-!
概要：二項積の反転した一点 Hom は、元の二つの係数の直積と厳密に同型。
方針：内部 Hom・単体の反転・宇宙持ち上げが二項積を保存する同型を使う。
規約：二射影は元の Kan 複体の fst・snd。使われ方：普遍 fiber の積比較の同値性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- Kan 複体の豊穣後合成は、元の内部 Hom の共変作用そのもの。 -/
lemma kanCoefficientPostcomposition (A : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) {K L : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}} (f : K ⟶ L) :
    eHomWhiskerLeft SSet A f = (ihom A.obj).map f := by
  apply uncurry_injective
  rw [uncurry_ihom_map, uncurry_eq]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨x, H⟩
  rfl

/-- 二項積の反転した一点 Hom を、同じ二射影の係数作用で分解する。 -/
def pointedTensorCoefficientIso (K L : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    (SSet.uliftFunctor.{u + 1, u}).obj
        (SimplicialCategory.sHom _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanTensorLeft K).obj L)).op ≅
      (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject K).op ⊗
        (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject L).op :=
  (SSet.uliftFunctor.{u + 1, u}).mapIso
    (CartesianMonoidalCategory.prodComparisonIso
      (ihom _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject.obj ⋙ SSet.opFunctor) K.obj L.obj) ≪≫
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso (SimplicialCategory.sHom _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject K).op
      (SimplicialCategory.sHom _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject L).op

/-- 係数同型の第一射影は、元の fst の反転した一点 Hom 作用。 -/
lemma pointedTensorCoefficientIso_fst (K L : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    (pointedTensorCoefficientIso K L).hom ≫ fst _ _ =
      (SSet.uliftFunctor.{u + 1, u}).map
        (SSet.opFunctor.map (eHomWhiskerLeft SSet _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject
          (show (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanTensorLeft K).obj L ⟶ K from fst K.obj L.obj))) := by
  have h : (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso
      (SimplicialCategory.sHom _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject K).op
      (SimplicialCategory.sHom _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject L).op).hom ≫ fst _ _ =
        (SSet.uliftFunctor.{u + 1, u}).map (fst _ _) := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    rfl
  calc
    _ = (SSet.uliftFunctor.{u + 1, u}).map
        ((CartesianMonoidalCategory.prodComparisonIso
          (ihom _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject.obj ⋙ SSet.opFunctor) K.obj L.obj).hom ≫ fst _ _) := by
      rw [pointedTensorCoefficientIso, Iso.trans_hom, Functor.mapIso_hom,
        Category.assoc, h, ← Functor.map_comp]
      rfl
    _ = (SSet.uliftFunctor.{u + 1, u}).map
        (SSet.opFunctor.map ((ihom _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject.obj).map (fst K.obj L.obj))) :=
      congrArg (SSet.uliftFunctor.{u + 1, u}).map
        (CartesianMonoidalCategory.prodComparison_fst
          (ihom _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject.obj ⋙ SSet.opFunctor) K.obj L.obj)
    _ = _ := congrArg (SSet.uliftFunctor.{u + 1, u}).map
      (congrArg SSet.opFunctor.map (kanCoefficientPostcomposition _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject
        (show (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanTensorLeft K).obj L ⟶ K from fst K.obj L.obj)).symm)

/-- 係数同型の第二射影も、元の snd の反転した一点 Hom 作用。 -/
lemma pointedTensorCoefficientIso_snd (K L : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    (pointedTensorCoefficientIso K L).hom ≫ snd _ _ =
      (SSet.uliftFunctor.{u + 1, u}).map
        (SSet.opFunctor.map (eHomWhiskerLeft SSet _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject
          (show (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanTensorLeft K).obj L ⟶ L from snd K.obj L.obj))) := by
  have h : (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso
      (SimplicialCategory.sHom _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject K).op
      (SimplicialCategory.sHom _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject L).op).hom ≫ snd _ _ =
        (SSet.uliftFunctor.{u + 1, u}).map (snd _ _) := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    rfl
  calc
    _ = (SSet.uliftFunctor.{u + 1, u}).map
        ((CartesianMonoidalCategory.prodComparisonIso
          (ihom _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject.obj ⋙ SSet.opFunctor) K.obj L.obj).hom ≫ snd _ _) := by
      rw [pointedTensorCoefficientIso, Iso.trans_hom, Functor.mapIso_hom,
        Category.assoc, h, ← Functor.map_comp]
      rfl
    _ = (SSet.uliftFunctor.{u + 1, u}).map
        (SSet.opFunctor.map ((ihom _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject.obj).map (snd K.obj L.obj))) :=
      congrArg (SSet.uliftFunctor.{u + 1, u}).map
        (CartesianMonoidalCategory.prodComparison_snd
          (ihom _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject.obj ⋙ SSet.opFunctor) K.obj L.obj)
    _ = _ := congrArg (SSet.uliftFunctor.{u + 1, u}).map
      (congrArg SSet.opFunctor.map (kanCoefficientPostcomposition _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject
        (show (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanTensorLeft K).obj L ⟶ L from snd K.obj L.obj)).symm)

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
