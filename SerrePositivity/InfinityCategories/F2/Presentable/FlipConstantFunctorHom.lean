module

public import SerrePositivity.InfinityCategories.F2.Presentable.FlipFunctorHom
public import SerrePositivity.InfinityCategories.F2.Presentable.ConstantEvaluationHomTransport

/-!
概要：定値図式への後合成と変数交換を Hom の定値化へ照合する。
方針：全関手の転置を計算し、同じ代表辺で端点を輸送する。
規約：関手の元の全パラメータを保持する。
使われ方：余極限関手の随伴の単位判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：定値図式族の変数交換は元の全関手頂点への定値射。
方針：二重の curry を展開して各次数の評価を比較する。
規約：全単体の等式である。
使われ方：Hom 比較の標的の同定。 -/
lemma flip_postcompose_constant {A K X : SSet.{u}} (V : A ⟶ X) :
    internalHomFlipHomEquiv A K X (V ≫ constantFunctorMap K X) =
      SSet.const (functorVertex V) := by
  change curry ((β_ A K).hom ≫ uncurry (V ≫ constantFunctorMap K X)) = _
  apply uncurry_injective
  rw [uncurry_curry, uncurry_natural_left,
    constantFunctorMap, uncurry_curry, uncurry_const_functorVertex]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro z
  rfl

/-- 概要：定値図式への後合成を交換すると、全関手圏での定値化になる。
方針：内部 Hom の各次数の評価を計算する。
規約：全パラメータの厳密な等式である。
使われ方：単位の全 Hom 公式の転置。 -/
lemma swap_postcompose_constant (A K X : SSet.{u}) :
    (ihom A).map (constantFunctorMap K X) ≫ (internalHomSwapIso A K X).hom =
      constantFunctorMap K ((ihom A).obj X) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro z
  apply CategoryTheory.Functor.functorHom_ext
  intro d α
  apply ConcreteCategory.hom_ext
  intro k
  apply CategoryTheory.Functor.functorHom_ext
  intro e β
  apply ConcreteCategory.hom_ext
  intro a
  change X.map (𝟙 e) (z.app e (α ≫ β) a) = z.app e (α ≫ β) a
  exact CategoryTheory.Functor.map_id_apply X e _

/-- 概要：定値後合成した Hom の変数交換は元の Hom の定値化。
方針：全関手の交換公式をホモトピー圏へ写し、端点の輸送を相殺する。
規約：同じ指定 Hom を保持する。
使われ方：余極限単位の全 Hom 対応。 -/
lemma flip_postcompose_constant_hom {A K X : SSet.{u}} [Quasicategory X]
    {U V : A ⟶ X} (α : FunctorHom U V) :
    F1B.kanFunctorHomCongr (flip_postcompose_constant U) (flip_postcompose_constant V)
      (flipFunctorHomEquiv (U ≫ constantFunctorMap K X) (V ≫ constantFunctorMap K X)
        ((hoFunctor.map ((ihom A).map (constantFunctorMap K X))).toFunctor.map α)) =
      constantFunctorHomMap K α := by
  change F1B.kanFunctorHomCongr (flip_postcompose_constant U) (flip_postcompose_constant V)
    ((hoFunctor.map (internalHomSwapIso A K X).hom).toFunctor.map
      ((hoFunctor.map ((ihom A).map (constantFunctorMap K X))).toFunctor.map α)) = _
  have h := CategoryTheory.Functor.congr_hom
    (congrArg (fun f ↦ (hoFunctor.map f).toFunctor) (swap_postcompose_constant A K X)) α
  rw [hoFunctor_map_comp_apply] at h
  simp only [F1B.kanFunctorHomCongr, Iso.homCongr_apply, eqToIso.inv, eqToIso.hom,
    constantFunctorHomMap]
  rw [h]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl,
    Category.id_comp, Category.comp_id]

end SerrePositivity.InfinityCategories.F2.Presentable
