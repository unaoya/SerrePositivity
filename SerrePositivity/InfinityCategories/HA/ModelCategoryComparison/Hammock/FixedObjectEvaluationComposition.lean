module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FixedObjectLocalizationEvaluation
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.HammockValueComposition

/-!
# 固定対象の局所化評価の元の合成則

概要：元の hammock の合成を同じ固定 Hom の合成へ送る。
方針：元の評価の合成則と中間対象の表示移送の相殺を使う。
規約：元の全点・同じ評価・同じ移送を保持する。
使われ方：自由 hammock の右比較の合成保存。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u uI vI uO
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FixedObjectDiagram.LocalizationObjects
open _root_.CategoryTheory
variable {I : Type uI} [Category.{vI} I] {D : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}}
  {O : Type uO} (T : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FixedObjectDiagram.LocalizationObjects D O)

lemma colimitValue_composePoint (i : I) (X Y Z : O) (n : SimplexCategoryᵒᵖ)
    (p : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph (D.obj i).weakEquivalences (T.original i X) (T.original i Y)).obj n)
    (q : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph (D.obj i).weakEquivalences (T.original i Y) (T.original i Z)).obj n) :
    (T.colimitValue i X Z).app n
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint (D.obj i).weakEquivalences (T.original i X) (T.original i Y)
          (T.original i Z) p q) =
      (T.colimitValue i X Y).app n p ≫ (T.colimitValue i Y Z).app n q := by
  change eqToHom (T.image_eq i X).symm ≫
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Zigzag.Value.colimitValue (D.obj i).weakEquivalences.Q
        (D.obj i).weakEquivalences.Q_inverts _ _).app n (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint _ _ _ _ p q) ≫
          eqToHom (T.image_eq i Z) =
    (eqToHom (T.image_eq i X).symm ≫
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Zigzag.Value.colimitValue (D.obj i).weakEquivalences.Q
        (D.obj i).weakEquivalences.Q_inverts _ _).app n p ≫ eqToHom (T.image_eq i Y)) ≫
    (eqToHom (T.image_eq i Y).symm ≫
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Zigzag.Value.colimitValue (D.obj i).weakEquivalences.Q
        (D.obj i).weakEquivalences.Q_inverts _ _).app n q ≫ eqToHom (T.image_eq i Z))
  rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Zigzag.Value.colimitValue_composePoint]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FixedObjectDiagram.LocalizationObjects
