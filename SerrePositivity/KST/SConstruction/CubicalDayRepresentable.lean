module
public import SerrePositivity.KST.SConstruction.CubicalDayCells

/-! # 元の表現可能立方体の Day tensor の比較
概要：二つの元の表現可能立方体の Day tensor を、連結した表現可能立方体へ比較する。
方針：元の全具体的射の tensor 作用を左 Kan 延長し、恒等 cell から逆射を作る。
規約：ulift Yoneda と元の cell を保持する。使われ方：necklace の各 bead の連結。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Opposite
open scoped MonoidalCategory.ExternalProduct

/-- 元の二つの具体的射を連結した、表現可能前層の二つの cell の作用。 -/
def cubicalDayCubePair (c d : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube) :
    cubicalYoneda.obj c ⊠ cubicalYoneda.obj d ⟶
      tensor _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCubeᵒᵖ ⋙ cubicalYoneda.obj (concreteCubeTensorObj c d) where
  app P := TypeCat.ofHom fun z => ULift.up (concreteCubeTensorMap z.1.down z.2.down)
  naturality {P Q} f := by
    apply ConcreteCategory.hom_ext
    intro z
    change ULift.up (concreteCubeTensorMap (f.1.unop ≫ z.1.down)
        (f.2.unop ≫ z.2.down)) =
      ULift.up (concreteCubeTensorMap f.1.unop f.2.unop ≫
        concreteCubeTensorMap z.1.down z.2.down)
    rw [concreteCubeTensorMap_comp]

/-- 元の二つの表現可能立方体の Day tensor から連結した表現可能立方体への射。 -/
def cubicalDayCubeProjection (c d : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube) :
    cubicalDayTensor (cubicalYoneda.obj c) (cubicalYoneda.obj d) ⟶
      cubicalYoneda.obj (concreteCubeTensorObj c d) :=
  cubicalDayTensorDesc (cubicalDayCubePair c d)

/-- 元の射からなる二つの cell に対して、比較射は同じ元の tensor 射を回収する。 -/
lemma cubicalDayCubeProjection_cell (c d a b : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube)
    (x : a ⟶ c) (y : b ⟶ d) :
    (cubicalDayCubeProjection c d).app (op (concreteCubeTensorObj a b))
        (cubicalDayTensorCell a b (ULift.up x) (ULift.up y)) =
      ULift.up (concreteCubeTensorMap x y) :=
  cubicalDayTensorDesc_cell (cubicalDayCubePair c d) a b (ULift.up x) (ULift.up y)

/-- 元の両恒等 cell の連結による、表現可能比較の逆向きの射。 -/
def cubicalDayCubeInclusion (c d : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube) :
    cubicalYoneda.obj (concreteCubeTensorObj c d) ⟶
      cubicalDayTensor (cubicalYoneda.obj c) (cubicalYoneda.obj d) :=
  cubicalCell (concreteCubeTensorObj c d)
    (cubicalDayTensorCell c d (ULift.up (𝟙 c)) (ULift.up (𝟙 d)))

/-- 表現可能立方体への比較は、元の連結立方体上で右逆を持つ。 -/
lemma cubicalDayCubeInclusion_projection (c d : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube) :
    cubicalDayCubeInclusion c d ≫ cubicalDayCubeProjection c d =
      𝟙 (cubicalYoneda.obj (concreteCubeTensorObj c d)) := by
  apply uliftYonedaEquiv.injective
  erw [uliftYonedaEquiv_comp]
  change (cubicalDayCubeProjection c d).app (op (concreteCubeTensorObj c d))
      (uliftYonedaEquiv (uliftYonedaEquiv.symm
        (cubicalDayTensorCell c d (ULift.up (𝟙 c)) (ULift.up (𝟙 d))))) = _
  rw [Equiv.apply_symm_apply, cubicalDayCubeProjection_cell, concreteCubeTensorMap_id]
  rfl

/-- 元の全ての二つの cell 上でも、連結比較の逆律が成り立つ。 -/
lemma cubicalDayCubeProjection_inclusion (c d : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube) :
    cubicalDayCubeProjection c d ≫ cubicalDayCubeInclusion c d =
      𝟙 (cubicalDayTensor (cubicalYoneda.obj c) (cubicalYoneda.obj d)) := by
  apply cubicalDayTensor_cell_hom_ext
  intro a b x y
  change (cubicalDayCubeInclusion c d).app (op (concreteCubeTensorObj a b))
      ((cubicalDayCubeProjection c d).app (op (concreteCubeTensorObj a b))
        (cubicalDayTensorCell a b x y)) = cubicalDayTensorCell a b x y
  erw [cubicalDayCubeProjection_cell c d a b x.down y.down]
  change (cubicalDayTensor (cubicalYoneda.obj c) (cubicalYoneda.obj d)).map
      (concreteCubeTensorMap x.down y.down).op
        (cubicalDayTensorCell c d (ULift.up (𝟙 c)) (ULift.up (𝟙 d))) = _
  erw [cubicalDayTensorCell_restrict]
  rfl

/-- 元の二つの表現可能立方体の Day tensor は、連結した表現可能立方体と同型。 -/
def cubicalDayCubeIso (c d : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube) :
    cubicalDayTensor (cubicalYoneda.obj c) (cubicalYoneda.obj d) ≅
      cubicalYoneda.obj (concreteCubeTensorObj c d) where
  hom := cubicalDayCubeProjection c d
  inv := cubicalDayCubeInclusion c d
  hom_inv_id := cubicalDayCubeProjection_inclusion c d
  inv_hom_id := cubicalDayCubeInclusion_projection c d

end SerrePositivity.KST.SConstruction
