module

public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.ConstantComparison

/-!
# 定値図式への実現比較の frame に関する自然性

概要：Hovey §5.4 の定値図式への比較を frame の族で自然に構成する。
方針：実際の Yoneda 拡張の単位と重みの一点比較の自然性を使う。
規約：実現の係数射は既存の Kan 拡張の関手的な射。
使われ方：定値図式の関手的な cofibrant 置換。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.SerrePositivity.HomotopyFunctionComplex

variable {C : Type v} [Category.{u} C] [HasColimitsOfSize.{0, u} C]
  {B B' : SimplexCategory ⥤ C}

/-- 概要：一点の実現の零次同型は frame の射に自然（Hovey §5.4）。
方針：表現可能対象の単位の自然性と一点同型への実現の自然性を使う。
規約：係数射は元の実現族の同じ射を使う。
使われ方：定値図式への比較の族を自然変換にする。 -/
lemma realizationPointIso_naturality (a : B ⟶ B') :
    (Realization.family.map a).app (⊤_ SSet.{u}) ≫ (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.realizationPointIso B').hom =
      (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.realizationPointIso B).hom ≫ a.app (SimplexCategory.mk 0) := by
  have h := congr_app (Realization.unit_naturality a) (SimplexCategory.mk 0)
  change a.app (SimplexCategory.mk 0) ≫
      ((Realization.representableIso B').app (SimplexCategory.mk 0)).hom =
    ((Realization.representableIso B).app (SimplexCategory.mk 0)).hom ≫
      (Realization.family.map a).app (uliftYoneda.{u, 0, 0}.obj (SimplexCategory.mk 0)) at h
  have hz : (Realization.family.map a).app
        (uliftYoneda.{u, 0, 0}.obj (SimplexCategory.mk 0)) ≫
      ((Realization.representableIso B').app (SimplexCategory.mk 0)).inv =
    ((Realization.representableIso B).app (SimplexCategory.mk 0)).inv ≫
      a.app (SimplexCategory.mk 0) := by
    apply (cancel_epi ((Realization.representableIso B).app (SimplexCategory.mk 0)).hom).mp
    rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id,
      Iso.hom_inv_id_assoc]
  have hn : (Realization.family.map a).app (⊤_ SSet.{u}) ≫
      (Realization.functor B').map _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.liftedZeroPointIso.inv =
    (Realization.functor B).map _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.liftedZeroPointIso.inv ≫ (Realization.family.map a).app
      (uliftYoneda.{u, 0, 0}.obj (SimplexCategory.mk 0)) :=
    ((Realization.family.map a).naturality _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.liftedZeroPointIso.inv).symm
  change (Realization.family.map a).app (⊤_ SSet.{u}) ≫
      (Realization.functor B').map _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.liftedZeroPointIso.inv ≫
        ((Realization.representableIso B').app (SimplexCategory.mk 0)).inv =
    ((Realization.functor B).map _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.liftedZeroPointIso.inv ≫
      ((Realization.representableIso B).app (SimplexCategory.mk 0)).inv) ≫ a.app _
  rw [← Category.assoc, hn, Category.assoc, hz, ← Category.assoc]

variable (K : Type u) [SmallCategory K]

/-- 概要：定値図式への比較の成分は実際の一点比較の実現（Hovey §5.4）。
方針：合成自然変換を各頂点で評価する。
規約：指定した零次の比較射をそのまま使う。
使われ方：係数 frame に関する比較の自然性。 -/
lemma pointwiseFrameComparison_app {Y : C}
    (α : B.obj (SimplexCategory.mk 0) ⟶ Y) (k : K) :
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseFrameComparison B K α).app k =
      (Realization.functor B).map ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.comparison K).app k) ≫ (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.realizationPointIso B).hom ≫ α := by
  change (Realization.functor B).map ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.comparison K).app k) ≫ 𝟙 _ ≫
    ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.realizationPointIso B).hom ≫ α) = _
  rw [Category.id_comp]

/-- 概要：定値図式への比較は frame と零次の射の族で自然（Hovey §5.4）。
方針：実現の自然性と一点の零次同型の自然性を合成する。
規約：零次の四角形の厳密な可換性を保持する。
使われ方：具体的な E 代数の定値図式置換の自然変換。 -/
lemma pointwiseFrameComparison_naturality (a : B ⟶ B') {Y Y' : C} (f : Y ⟶ Y')
    (α : B.obj (SimplexCategory.mk 0) ⟶ Y) (α' : B'.obj (SimplexCategory.mk 0) ⟶ Y')
    (hα : a.app (SimplexCategory.mk 0) ≫ α' = α ≫ f) :
    Functor.whiskerLeft (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K) (Realization.family.map a) ≫
        _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseFrameComparison B' K α' =
      _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseFrameComparison B K α ≫ (Functor.const K).map f := by
  apply NatTrans.ext
  funext k
  simp only [NatTrans.comp_app, _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseFrameComparison_app]
  change (Realization.family.map a).app _ ≫
      (Realization.functor B').map ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.comparison K).app k) ≫ (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.realizationPointIso B').hom ≫ α' = _
  have hp : (Realization.family.map a).app ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K).obj k) ≫
      (Realization.functor B').map ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.comparison K).app k) =
    (Realization.functor B).map ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.comparison K).app k) ≫
      (Realization.family.map a).app (⊤_ SSet.{u}) :=
    ((Realization.family.map a).naturality ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.comparison K).app k)).symm
  rw [← Category.assoc, ← Category.assoc, hp]
  simp only [Category.assoc]
  rw [← Category.assoc ((Realization.family.map a).app (⊤_ SSet.{u}))
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.realizationPointIso B').hom α', _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.realizationPointIso_naturality]
  simp only [Category.assoc]
  rw [hα]
  rfl

end SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight
