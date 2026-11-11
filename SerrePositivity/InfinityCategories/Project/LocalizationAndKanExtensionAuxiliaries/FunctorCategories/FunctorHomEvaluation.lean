module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConstantFunctor
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomCorrespondence

/-!
概要：h Fun の二胞体を各頂点で評価し、定値の前合成と比較する。
方針：内部 Hom の評価の射を h に移し、端点の表示を明示して輸送する。
規約：quasicategory 性や随伴の存在は不要。
使われ方：指定単位の各点の成分と定値パラメータ族の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories

/-- 概要：関手を x で評価して定値関手へ送る射は定値 x での前合成に等しい。
方針：各関手単体の自然性と x の定値単体の引き戻しを計算する。
規約：パラメータ A と始域 K を区別する。
使われ方：単位の各点の評価をパラメータ付き二胞体に戻す。 -/
lemma evaluateFunctorAt_constantFunctorMap (A : SSet.{u}) {K X : SSet.{u}} (x : K _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) x ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap A X =
      (pre (SSet.const x : A ⟶ K)).app X := by
  apply uncurry_injective
  rw [uncurry_natural_left]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap, uncurry_curry]
  have hp := uncurry_pre_app X (𝟙 ((ihom K).obj X)) (SSet.const x : A ⟶ K)
  simp only [Category.id_comp] at hp
  rw [hp]
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro z
  rfl

/-- 概要：h Fun の二胞体の頂点 x での評価。
方針：評価の関手で写し、両端を U(x),V(x) の表示へ輸送する。
規約：ホモトピー圏の射を返し、可逆性は要求しない。
使われ方：単位の各点での成分の定義。 -/
def functorHomEvaluate {K X : SSet.{u}} {U V : K ⟶ X}
    (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom U V) (x : K _⦋0⦌) :
    (HomotopyCategory.mk (U.app (Opposite.op ⦋0⦌) x) : hoFunctor.obj X) ⟶
      HomotopyCategory.mk (V.app (Opposite.op ⦋0⦌) x) :=
  eqToHom (congrArg HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex x U)).symm ≫
    (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) x)).toFunctor.map α ≫
      eqToHom (congrArg HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex x V))

/-- 概要：二胞体の評価は恒等二胞体を保つ。
方針：評価の関手性と端点の輸送の相殺。
規約：U は任意の関手。
使われ方：単位の公式の恒等射での計算。 -/
lemma functorHomEvaluate_id {K X : SSet.{u}} (U : K ⟶ X) (x : K _⦋0⦌) :
    functorHomEvaluate (𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex U))) x = 𝟙 _ := by
  simp [functorHomEvaluate]

/-- 概要：二胞体の評価は縦合成を保つ。
方針：評価の関手性と中間の端点の輸送の相殺。
規約：可逆でない二胞体も扱う。
使われ方：単位比較の各点の公式の合成。 -/
lemma functorHomEvaluate_comp {K X : SSet.{u}} {U V W : K ⟶ X}
    (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom U V) (β : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom V W) (x : K _⦋0⦌) :
    functorHomEvaluate (α ≫ β) x = functorHomEvaluate α x ≫ functorHomEvaluate β x := by
  simp [functorHomEvaluate, Category.assoc]

/-- 概要：二胞体の点での評価の定値族は、定値射による前合成に一致する。
方針：単体的な評価と定値関手の等式を h に移し、端点の輸送を相殺する。
規約：定値関手の合成の同一視は既存の constantFunctorCompIso を使う。
使われ方：単位の各点の成分とパラメータ付きの制限の接続。 -/
lemma functorHomEvaluate_constantFunctorHomMap (A : SSet.{u}) {K X : SSet.{u}}
    {U V : K ⟶ X} (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom U V) (x : K _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.constantFunctorCompIso A x U).inv ≫
      (hoFunctor.map ((pre (SSet.const x : A ⟶ K)).app X)).toFunctor.map α ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.constantFunctorCompIso A x V).hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap A (functorHomEvaluate α x) := by
  have h := congrArg (fun k : (ihom K).obj X ⟶ (ihom A).obj X ↦ (hoFunctor.map k).toFunctor)
    (evaluateFunctorAt_constantFunctorMap (X := X) A x)
  simp only [Functor.map_comp] at h
  have hh := CategoryTheory.Functor.congr_hom h α
  change (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap A X)).toFunctor.map
    ((hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) x)).toFunctor.map α) = _ at hh
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap, functorHomEvaluate, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.constantFunctorCompIso,
    eqToIso.inv, eqToIso.hom, Functor.map_comp, eqToHom_map]
  rw [hh]
  simp

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
