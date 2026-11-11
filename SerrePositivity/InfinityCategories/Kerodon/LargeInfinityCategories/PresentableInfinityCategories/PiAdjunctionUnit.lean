module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PiFunctorMap
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitHomFormula

/-!
概要：小さい族の元の全随伴の単位を全直積へまとめる。
方針：各射影への前合成を全 Hom 比較で戻し、単位 Hom 比較の各成分を計算する。
規約：全随伴の存在を追加入力にしない。
使われ方：小さい全直積の反映の構成。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
variable {ι : Type u} {C D : ι → SSet.{u + 1}}
  [∀ i, Quasicategory (C i)] [∀ i, Quasicategory (D i)]
  {F : ∀ i, C i ⟶ D i} {R : ∀ i, D i ⟶ C i}

/-- 概要：全随伴の単位の族を直積の各射影で前合成する。
方針：同じ各単位を全パラメーターへ制限する。
規約：元の関手を保持する。使われ方：全直積の単位の成分。 -/
def piAdjunctionUnitComponents (a : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (F i) (R i)) :
    ∀ i, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom ((𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSet C)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSetProjection C i)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSetMap F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSetMap R) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSetProjection C i) := by
  intro i
  change _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSetProjection C i) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSetProjection C i ≫ F i ≫ R i)
  exact (hoFunctor.map ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSetProjection C i)).app (C i))).toFunctor.map (a i).unitHom

/-- 概要：元の小さい族の全単位を直積の全単位候補へまとめる。
方針：全成分の二胞体を全 Hom 比較の逆で戻す。
規約：余単位は入力にしない。使われ方：直積の全随伴の単位判定。 -/
def piAdjunctionUnit (a : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (F i) (R i)) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSet C)) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSetMap F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSetMap R) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorHomPiEquiv _ _).symm (piAdjunctionUnitComponents a)

/-- 概要：構成した全単位の各成分は元の単位の射影への前合成。
方針：全 Hom 比較の逆条件を指定成分で評価する。
規約：元の全二胞体の等式。使われ方：単位 Hom 比較の成分計算。 -/
lemma piAdjunctionUnit_projection (a : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (F i) (R i)) (i : ι) :
    (hoFunctor.map ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSet C)).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSetProjection C i))).toFunctor.map
      (piAdjunctionUnit a) =
      (hoFunctor.map ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSetProjection C i)).app (C i))).toFunctor.map (a i).unitHom := by
  change @Eq (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSetProjection C i) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSetProjection C i ≫ F i ≫ R i)) _ _
  have h := congrFun ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorHomPiEquiv _ _).apply_symm_apply
    (piAdjunctionUnitComponents a)) i
  simpa only [piAdjunctionUnit, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorHomPiEquiv_apply, piAdjunctionUnitComponents,
    id_eq, Category.id_comp, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSetMap_projection] using h

/-- 概要：直積の単位 Hom 比較は元の各随伴の単位 Hom 比較へ分解される。
方針：全二胞体の前後合成の公式と構成した単位の各射影を使う。
規約：任意の全 quasicategory パラメーター A。
使われ方：直積の単位 Hom 比較の全単射性。 -/
lemma piAdjunctionUnit_homMap_components (a : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (F i) (R i))
    {A : SSet.{u + 1}} [Quasicategory A] (U : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSet C) (V : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSet D)
    (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (U ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSetMap F) V) (i : ι) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorHomPiEquiv U (V ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSetMap R) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatUnitHomMap (piAdjunctionUnit a) U V α) i =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatUnitHomMap (a i).unitHom (U ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSetProjection C i) (V ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSetProjection D i)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorHomPiEquiv (U ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSetMap F) V α i) := by
  have hi := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorHomPiEquiv_postcomp R α i
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorHomPiEquiv_apply] at hi
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorHomPiEquiv_apply, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatUnitHomMap_formula,
    CategoryTheory.Functor.map_comp, ← _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorHom_pre_post, piAdjunctionUnit_projection,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorHom_pre_comp, hi]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
