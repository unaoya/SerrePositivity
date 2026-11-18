module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FixedObjectLocalizationEvaluation
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LocalizationValue
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PrecompositionTensor

/-!
# 元の固定対象の局所化 Hom の移送同型

概要：元の対象表示の等式による Hom の移送は実際の同型となる。
方針：同じ二つの端点の等式を逆向きに合成して戻す。
規約：元の homTransport と元の colimitValue を保持する。
使われ方：自由次数の同じ局所化評価から既存 DK Hom への右射の弱比較。
-/

@[expose] public section
universe u uI vI uO
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FixedObjectDiagram.LocalizationObjects
open _root_.CategoryTheory _root_.SerrePositivity.InfinityCategories

variable {I : Type uI} [Category.{vI} I] {D : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}}
  {O : Type uO} (T : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FixedObjectDiagram.LocalizationObjects D O)

def homTransportEquiv (i : I) (X Y : O) :
    ((D.obj i).weakEquivalences.Q.obj (T.original i X) ⟶
      (D.obj i).weakEquivalences.Q.obj (T.original i Y)) ≃ (T.localized i X ⟶ T.localized i Y) where
  toFun := T.homTransport i X Y
  invFun f := eqToHom (T.image_eq i X) ≫ f ≫ eqToHom (T.image_eq i Y).symm
  left_inv f := by
    change eqToHom (T.image_eq i X) ≫
      (eqToHom (T.image_eq i X).symm ≫ f ≫ eqToHom (T.image_eq i Y)) ≫
        eqToHom (T.image_eq i Y).symm = f
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl,
      Category.id_comp, Category.comp_id]
  right_inv f := by
    change eqToHom (T.image_eq i X).symm ≫
      (eqToHom (T.image_eq i X) ≫ f ≫ eqToHom (T.image_eq i Y).symm) ≫
        eqToHom (T.image_eq i Y) = f
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl,
      Category.id_comp, Category.comp_id]

def homTransportIso (i : I) (X Y : O) :
    (Functor.const SimplexCategoryᵒᵖ).obj
      ((D.obj i).weakEquivalences.Q.obj (T.original i X) ⟶
        (D.obj i).weakEquivalences.Q.obj (T.original i Y)) ≅
      (T.homSimplicialDiagram X Y).obj i :=
  (Functor.const SimplexCategoryᵒᵖ).mapIso (Equiv.toIso (T.homTransportEquiv i X Y))

lemma colimitValue_weak_of_localizationValue (i : I) (X Y : O)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.localizationValue (D.obj i).weakEquivalences
      (T.original i X) (T.original i Y))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (T.colimitValue i X Y) :=
  h.comp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso (T.homTransportIso i X Y)).isWeakHomotopyEquivalence

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FixedObjectDiagram.LocalizationObjects
