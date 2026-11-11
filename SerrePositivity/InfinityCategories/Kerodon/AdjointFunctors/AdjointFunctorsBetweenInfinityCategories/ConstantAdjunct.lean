module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.AdjunctParameterNaturality
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.MappingParameterNaturality

/-!
概要：定値関手間の Hom についての adjunct 対応。
方針：任意の関手 U,V の対応に、定値関手と後合成の同一視を補う。
規約：後合成による定値関手の保存を定義上の等式とは仮定しない。
使われ方：Kerodon Prop 6.2.1.17（Tag 02F1） の二つの写像空間の端点。

対応節は Kerodon 6.2（Tag 02EH）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories

/-- 概要：定値関手間の h Fun の Hom。
方針：既存の関手頂点で両端を指定する。
規約：パラメータ A に quasicategory 性は不要。
使われ方：写像空間の族の adjunct 対応。 -/
abbrev ConstantFunctorHom (A X : SSet.{u}) (x y : X _⦋0⦌) :=
  (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const x : A ⟶ X)) :
    hoFunctor.obj ((ihom A).obj X)) ⟶
      SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const y))

/-- 概要：定値関手の後合成と、像の頂点での定値関手の同一視。
方針：SSet.const_comp を h Fun の対象の同型に移す。
規約：同一視を明示する。A の quasicategory 性は不要。
使われ方：adjunct 対応の写像空間の端点への表示。 -/
def constantFunctorCompIso (A : SSet.{u}) {X Y : SSet.{u}} (x : X _⦋0⦌) (F : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((SSet.const x : A ⟶ X) ≫ F)
      (SSet.const (F.app (Opposite.op ⦋0⦌) x)) :=
  eqToIso (congrArg (fun H : A ⟶ Y ↦ SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex H))
    (SSet.const_comp x F))

namespace QCatAdjunction

/-- 概要：定値関手間の Hom の adjunct 全単射。
方針：一般の対応の前後で定値関手の合成の同一視を行う。
規約：A は quasicategory、F(x),G(y) は指定された関手の頂点の像。
使われ方：Kerodon Prop 6.2.1.17（Tag 02F1） の写像空間のパラメータ付き表示。 -/
def constantHomEquiv {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F G)
    (A : SSet.{u}) [Quasicategory A] (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    ConstantFunctorHom A Y (F.app (Opposite.op ⦋0⦌) x) y ≃
      ConstantFunctorHom A X x (G.app (Opposite.op ⦋0⦌) y) :=
  ((constantFunctorCompIso A x F).symm.homCongr (Iso.refl _)).trans
    ((a.homEquiv (SSet.const x : A ⟶ X) (SSet.const y)).trans
      ((Iso.refl _).homCongr (constantFunctorCompIso A y G)))

/-- 概要：定値関手間の adjunct 対応はパラメータの前合成に自然。
方針：一般の自然性と対象の同一視の輸送を合わせる。
規約：A,B は quasicategory、i は任意の射。
使われ方：二つの写像空間の間の実際の射とホモトピー逆の構成。 -/
lemma constantHomEquiv_precomp {A B X Y : SSet.{u}}
    [Quasicategory A] [Quasicategory B] [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F G) (i : A ⟶ B)
    (x : X _⦋0⦌) (y : Y _⦋0⦌)
    (α : ConstantFunctorHom B Y (F.app (Opposite.op ⦋0⦌) x) y) :
    a.constantHomEquiv A x y (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomPrecomp i α) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomPrecomp i (a.constantHomEquiv B x y α) := by
  simp only [constantHomEquiv, Equiv.trans_apply, Iso.homCongr_apply,
    Iso.symm_inv, Iso.refl_hom, Iso.refl_inv, Category.id_comp, Category.comp_id]
  unfold constantFunctorCompIso _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomPrecomp
  simp only [eqToIso.hom, Functor.map_comp, eqToHom_map]
  have hn := a.homEquiv_precomp i (SSet.const x : B ⟶ X) (SSet.const y)
    ((constantFunctorCompIso B x F).hom ≫ α)
  simp only [constantFunctorCompIso, eqToIso.hom, Functor.map_comp, eqToHom_map] at hn
  simp only [SSet.comp_const] at hn
  exact congrArg (· ≫ (constantFunctorCompIso A y G).hom) hn

/-- 概要：定値関手間の逆 adjunct 対応もパラメータの前合成に自然。
方針：順対応の単射性と自然性、両逆の式を使う。
規約：パラメータ A,B は quasicategory。
使われ方：写像空間の比較射のホモトピー逆の構成。 -/
lemma constantHomEquiv_symm_precomp {A B X Y : SSet.{u}}
    [Quasicategory A] [Quasicategory B] [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F G) (i : A ⟶ B)
    (x : X _⦋0⦌) (y : Y _⦋0⦌)
    (α : ConstantFunctorHom B X x (G.app (Opposite.op ⦋0⦌) y)) :
    (a.constantHomEquiv A x y).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomPrecomp i α) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomPrecomp i ((a.constantHomEquiv B x y).symm α) := by
  apply (a.constantHomEquiv A x y).injective
  rw [Equiv.apply_symm_apply, constantHomEquiv_precomp, Equiv.apply_symm_apply]

end QCatAdjunction
end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
