module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryDiagramMixedHom

/-!
概要：通常の図式の列と底の図式を、同じ混合作用で対角の通常の QCat 値関手にする。
方針：元の豊穣混合作用の単位・合成則を通常の射へ戻す。
規約：同じ底の射と元の strict 図式の射を保持する。
使われ方：自然変換の辺の実現と元の prism の全単体の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories

/-- 通常の図式の列を、元の底と同じ strict 変換の混合作用で対角評価する。 -/
def quasicategoryDiagramDiagonalFunctor
    {C J : Type u} [Category.{u} C] [Category.{u} J]
    (A : J ⥤ C) (R : J ⥤ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryDiagramCategory C) : J ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u} where
  obj j := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryDiagramValue (R.obj j) (A.obj j)
  map {i j} f := (eHomEquiv SSet.{u}).symm
    (eHomEquiv SSet.{u} (R.map f) ≫ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryDiagramMixedHom (A.map f) (R.obj i) (R.obj j))
  map_id j := by
    apply (eHomEquiv SSet.{u}).injective
    simp only [Equiv.apply_symm_apply, R.map_id, A.map_id, eHomEquiv_id]
    exact _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryDiagramMixedHom_id (R.obj j) (A.obj j)
  map_comp {i j k} f g := by
    apply (eHomEquiv SSet.{u}).injective
    simp only [Equiv.apply_symm_apply, R.map_comp, A.map_comp, eHomEquiv_comp]
    simp only [Category.assoc]
    rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryDiagramMixedHom_comp, tensorHom_comp_tensorHom_assoc]

/-- 同じ通常の対角関手は、添字の通常の前合成を厳密に保つ。 -/
lemma quasicategoryDiagramDiagonalFunctor_precomp
    {C J K : Type u} [Category.{u} C] [Category.{u} J] [Category.{u} K]
    (A : J ⥤ C) (R : J ⥤ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryDiagramCategory C) (k : K ⥤ J) :
    quasicategoryDiagramDiagonalFunctor (k ⋙ A) (k ⋙ R) =
      k ⋙ quasicategoryDiagramDiagonalFunctor A R := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories
