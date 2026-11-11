module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitHomFormula
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomEvaluation

/-!
概要：指定単位の定値関手間の比較を各点の単位成分で表示する。
方針：定値射での制限と評価の定値族の一致を使い、後合成の端点の輸送を揃える。
規約：単位の普遍性も随伴の存在も仮定しない。
使われ方：Kerodon Cor 6.2.6.5（Tag 02FX） の各点の標準比較の公式。

対応節は Kerodon 6.2（Tag 02EH）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories

/-- 概要：h Fun の指定単位の各点の成分。
方針：単位の二胞体を始域の頂点で評価する。
規約：hX の x→G(F(x)) の射。
使われ方：各点の写像空間の単位による前合成。 -/
def qcatUnitComponent {X Y : SSet.{u}} {F : X ⟶ Y} {G : Y ⟶ X}
    (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G)) (x : X _⦋0⦌) :
    (HomotopyCategory.mk x : hoFunctor.obj X) ⟶
      HomotopyCategory.mk (G.app (Opposite.op ⦋0⦌) (F.app (Opposite.op ⦋0⦌) x)) :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate η x

/-- 概要：指定単位による定値関手間の Hom 比較。
方針：一般の単位比較に定値関手の合成の端点の同一視を補う。
規約：パラメータ A は quasicategory。
使われ方：各点の単位比較のパラメータ族での認識。 -/
def constantUnitHomMap {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G))
    (A : SSet.{u}) [Quasicategory A] (x : X _⦋0⦌) (y : Y _⦋0⦌)
    (α : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ConstantFunctorHom A Y (F.app (Opposite.op ⦋0⦌) x) y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ConstantFunctorHom A X x (G.app (Opposite.op ⦋0⦌) y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatUnitHomMap η (SSet.const x : A ⟶ X) (SSet.const y)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.constantFunctorCompIso A x F).hom ≫ α) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.constantFunctorCompIso A y G).hom

/-- 概要：定値関手間の単位比較は各点の単位成分と G の作用で表される。
方針：定値射での単位の制限を評価の定値族に置き換え、合成の輸送を相殺する。
規約：単位の候補 η に普遍性は要求しない。
使われ方：各点の写像空間比較と h Fun の族の比較の接続。 -/
lemma constantUnitHomMap_formula {A X Y : SSet.{u}}
    [Quasicategory A] [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G))
    (x : X _⦋0⦌) (y : Y _⦋0⦌)
    (α : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ConstantFunctorHom A Y (F.app (Opposite.op ⦋0⦌) x) y) :
    constantUnitHomMap η A x y α =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap A (qcatUnitComponent η x) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.constantFunctorCompIso A (F.app (Opposite.op ⦋0⦌) x) G).inv ≫
          (hoFunctor.map ((ihom A).map G)).toFunctor.map α ≫
            (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.constantFunctorCompIso A y G).hom := by
  unfold constantUnitHomMap qcatUnitComponent
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatUnitHomMap_formula, Functor.map_comp,
    ← _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate_constantFunctorHomMap A η x]
  simp [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.constantFunctorCompIso, eqToHom_map, Category.assoc]
  exact (Category.id_comp _).symm

/-- 概要：随伴の単位による定値 Hom 比較は既存の adjunct 全単射の順写像。
方針：二つの定義で同じ双圏の単位の公式を計算する。
規約：随伴の単位をそのまま用いる。
使われ方：標準的な単位比較と既存の写像空間同値を照合する。 -/
lemma constantUnitHomMap_of_adjunction {A X Y : SSet.{u}}
    [Quasicategory A] [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F G)
    (x : X _⦋0⦌) (y : Y _⦋0⦌)
    (α : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ConstantFunctorHom A Y (F.app (Opposite.op ⦋0⦌) x) y) :
    constantUnitHomMap a.unitHom A x y α = a.constantHomEquiv A x y α := by
  simp only [constantUnitHomMap, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction.constantHomEquiv, Equiv.trans_apply,
    Iso.homCongr_apply, Iso.symm_inv, Iso.refl_hom, Iso.refl_inv,
    Category.id_comp, Category.comp_id]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
