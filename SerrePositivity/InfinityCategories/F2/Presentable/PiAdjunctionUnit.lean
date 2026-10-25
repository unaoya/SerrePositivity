module

public import SerrePositivity.InfinityCategories.F2.Presentable.PiFunctorMap
public import SerrePositivity.InfinityCategories.F1B.Adjunction.UnitHomFormula

/-!
概要：小さい族の元の全随伴の単位を全直積へまとめる。
方針：各射影への前合成を全 Hom 比較で戻し、単位 Hom 比較の各成分を計算する。
規約：全随伴の存在を追加入力にしない。
使われ方：小さい全直積の反映の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable
variable {ι : Type u} {C D : ι → SSet.{u + 1}}
  [∀ i, Quasicategory (C i)] [∀ i, Quasicategory (D i)]
  {F : ∀ i, C i ⟶ D i} {R : ∀ i, D i ⟶ C i}

/-- 概要：全随伴の単位の族を直積の各射影で前合成する。
方針：同じ各単位を全パラメーターへ制限する。
規約：元の関手を保持する。使われ方：全直積の単位の成分。 -/
def piAdjunctionUnitComponents (a : ∀ i, QCatAdjunction (F i) (R i)) :
    ∀ i, FunctorHom ((𝟙 (piSSet C)) ≫ piSSetProjection C i)
      ((piSSetMap F ≫ piSSetMap R) ≫ piSSetProjection C i) := by
  intro i
  change FunctorHom (piSSetProjection C i) (piSSetProjection C i ≫ F i ≫ R i)
  exact (hoFunctor.map ((pre (piSSetProjection C i)).app (C i))).toFunctor.map (a i).unitHom

/-- 概要：元の小さい族の全単位を直積の全単位候補へまとめる。
方針：全成分の二胞体を全 Hom 比較の逆で戻す。
規約：余単位は入力にしない。使われ方：直積の全随伴の単位判定。 -/
def piAdjunctionUnit (a : ∀ i, QCatAdjunction (F i) (R i)) :
    FunctorHom (𝟙 (piSSet C)) (piSSetMap F ≫ piSSetMap R) :=
  (functorHomPiEquiv _ _).symm (piAdjunctionUnitComponents a)

/-- 概要：構成した全単位の各成分は元の単位の射影への前合成。
方針：全 Hom 比較の逆条件を指定成分で評価する。
規約：元の全二胞体の等式。使われ方：単位 Hom 比較の成分計算。 -/
lemma piAdjunctionUnit_projection (a : ∀ i, QCatAdjunction (F i) (R i)) (i : ι) :
    (hoFunctor.map ((ihom (piSSet C)).map (piSSetProjection C i))).toFunctor.map
      (piAdjunctionUnit a) =
      (hoFunctor.map ((pre (piSSetProjection C i)).app (C i))).toFunctor.map (a i).unitHom := by
  change @Eq (FunctorHom (piSSetProjection C i) (piSSetProjection C i ≫ F i ≫ R i)) _ _
  have h := congrFun ((functorHomPiEquiv _ _).apply_symm_apply
    (piAdjunctionUnitComponents a)) i
  simpa only [piAdjunctionUnit, functorHomPiEquiv_apply, piAdjunctionUnitComponents,
    id_eq, Category.id_comp, Category.assoc, piSSetMap_projection] using h

/-- 概要：直積の単位 Hom 比較は元の各随伴の単位 Hom 比較へ分解される。
方針：全二胞体の前後合成の公式と構成した単位の各射影を使う。
規約：任意の全 quasicategory パラメーター A。
使われ方：直積の単位 Hom 比較の全単射性。 -/
lemma piAdjunctionUnit_homMap_components (a : ∀ i, QCatAdjunction (F i) (R i))
    {A : SSet.{u + 1}} [Quasicategory A] (U : A ⟶ piSSet C) (V : A ⟶ piSSet D)
    (α : FunctorHom (U ≫ piSSetMap F) V) (i : ι) :
    functorHomPiEquiv U (V ≫ piSSetMap R) (qcatUnitHomMap (piAdjunctionUnit a) U V α) i =
      qcatUnitHomMap (a i).unitHom (U ≫ piSSetProjection C i) (V ≫ piSSetProjection D i)
        (functorHomPiEquiv (U ≫ piSSetMap F) V α i) := by
  have hi := functorHomPiEquiv_postcomp R α i
  simp only [functorHomPiEquiv_apply] at hi
  simp only [functorHomPiEquiv_apply, qcatUnitHomMap_formula,
    CategoryTheory.Functor.map_comp, ← functorHom_pre_post, piAdjunctionUnit_projection,
    ← functorHom_pre_comp, hi]

end SerrePositivity.InfinityCategories.F2.Presentable
