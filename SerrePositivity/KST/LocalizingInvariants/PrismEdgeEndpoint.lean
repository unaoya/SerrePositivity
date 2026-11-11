module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.CurryHomotopy

/-!
概要：辺でパラメーター付けた prism の二端は、元の端点の定値族に制限される。
方針：直積の制限と定値射の合成を計算し、辺の元の端点条件を使う。
規約：辺の代表や端点を選び直さない。使われ方：後合成 prism の端点三角形。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

lemma prismEdge_source {A B : SSet.{u}} {x y : B _⦋0⦌} (e : B.Edge x y) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.sliceMap (A := A) (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) ≫
      (A ◁ SSet.yonedaEquiv.symm e.edge) = lift (𝟙 A) (SSet.const x) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.sliceMap, lift_whiskerLeft, SSet.const_comp]
  have he : (SSet.yonedaEquiv.symm e.edge).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = x := by
    have hb : stdSimplex.obj₀Equiv.symm (0 : Fin 2) =
        stdSimplex.objEquiv.symm (SimplexCategory.δ (1 : Fin 2)) := by
      apply SSet.stdSimplex.ext
      intro i
      fin_cases i
      rfl
    rw [hb, SSet.yonedaEquiv_symm_app_objEquiv_symm]
    exact e.src_eq
  rw [he]

lemma prismEdge_target {A B : SSet.{u}} {x y : B _⦋0⦌} (e : B.Edge x y) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.sliceMap (A := A) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) ≫
      (A ◁ SSet.yonedaEquiv.symm e.edge) = lift (𝟙 A) (SSet.const y) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.sliceMap, lift_whiskerLeft, SSet.const_comp]
  have he : (SSet.yonedaEquiv.symm e.edge).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = y := by
    have hb : stdSimplex.obj₀Equiv.symm (1 : Fin 2) =
        stdSimplex.objEquiv.symm (SimplexCategory.δ (0 : Fin 2)) := by
      apply SSet.stdSimplex.ext
      intro i
      fin_cases i
      rfl
    rw [hb, SSet.yonedaEquiv_symm_app_objEquiv_symm]
    exact e.tgt_eq
  rw [he]

end SerrePositivity.KST.LocalizingInvariants
