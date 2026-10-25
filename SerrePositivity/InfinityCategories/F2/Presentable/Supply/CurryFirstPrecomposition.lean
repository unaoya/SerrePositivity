module

public import SerrePositivity.InfinityCategories.F2.Presentable.Supply.CurryPrecomposition

/-!
概要：指定 Hom と指定同型の curry は第一変数の制限と両立する。
方針：全関手空間の可換式を正規化 Hom 作用へ移す。
規約：元の Hom・同型・制限関手を保持する。
使われ方：P-12 の共同実現と単体添字関手の制限との照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：元の指定 Hom を同じ全関手で後合成する。
方針：内部 Hom の共変作用を元の両端点へ正規化する。
規約：任意の単体集合を許す。使われ方：curry 後の値域側の制限。 -/
def postcomposeFunctorHom {A X Y : SSet.{u}} (q : X ⟶ Y) {F G : A ⟶ X}
    (α : FunctorHom F G) : FunctorHom (F ≫ q) (G ≫ q) :=
  normalizedVertexHomMap ((ihom A).map q) (x := functorVertex F) (y := functorVertex G)
    (x' := functorVertex (F ≫ q)) (y' := functorVertex (G ≫ q)) rfl rfl α

/-- 概要：指定同型の後合成の順方向は同じ指定 Hom の後合成。
方針：等式同型による正規化を展開する。
規約：元の同型を使う。使われ方：値域制限した比較同型の Hom の計算。 -/
lemma functorIsoPostcomp_hom {A X Y : SSet.{u}} (q : X ⟶ Y)
    {F G : A ⟶ X} (e : FunctorIso F G) :
    (e.postcomp q).hom = postcomposeFunctorHom q e.hom := by
  simp only [FunctorIso.postcomp, Iso.trans_hom, Iso.symm_hom,
    postcomposeFunctorHom, normalizedVertexHomMap]
  rfl

/-- 概要：全関手空間の curry は第一変数の前合成と厳密に両立する。
方針：二重評価で同じ関手単体の作用を計算する。
規約：quasicategory 性は不要。使われ方：添字制限と共同実現の Hom の比較。 -/
lemma functorSpaceCurryMap_precompose_first {A A' B X : SSet.{u}} (q : A' ⟶ A) :
    (pre (q ▷ B)).app X ≫ functorSpaceCurryMap A' B X =
      functorSpaceCurryMap A B X ≫ (ihom B).map ((pre q).app X) := by
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_natural_right]
  unfold functorSpaceCurryMap
  rw [uncurry_curry, uncurry_curry]
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_pre_app, uncurry_curry, uncurry_curry]
  rw [← Category.assoc, associator_inv_naturality_right, Category.assoc,
    id_tensor_pre_app_comp_ev, ← associator_inv_naturality_left_assoc]

/-- 概要：指定 Hom の curry は第一変数の制限を値域側の後合成へ移す。
方針：元の二つの全関手空間の作用を同定し端点移送を正規化する。
規約：指定された元の射を保持する。使われ方：添字制限後の実現比較の Hom。 -/
lemma curryFunctorHom_precompose_first {A A' B X : SSet.{u}} (q : A' ⟶ A)
    {f g : A ⊗ B ⟶ X} (α : FunctorHom f g) :
    F1B.kanFunctorHomCongr (curry_pre_app q f).symm (curry_pre_app q g).symm
      (curryFunctorHom (precomposeFunctorHom (q ▷ B) α)) =
      postcomposeFunctorHom ((pre q).app X) (curryFunctorHom α) := by
  simp only [curryFunctorHom_eq_normalizedMap]
  rw [kanFunctorHomCongr_normalizedMap]
  unfold precomposeFunctorHom postcomposeFunctorHom
  rw [normalizedVertexHomMap_comp, normalizedVertexHomMap_comp]
  have hm : HEq
      ((hoFunctor.map ((pre (q ▷ B)).app X ≫ functorSpaceCurryMap A' B X)).toFunctor.map α)
      ((hoFunctor.map (functorSpaceCurryMap A B X ≫
        (ihom B).map ((pre q).app X))).toFunctor.map α) := by
    rw [functorSpaceCurryMap_precompose_first]
  exact eq_of_heq ((normalizedVertexHomMap_heq _ _ _ α).trans
    (hm.trans (normalizedVertexHomMap_heq _ _ _ α).symm))

/-- 概要：指定同型の curry は第一変数の制限を値域側の後合成へ移す。
方針：元の Hom の curry の前合成公式を使う。
規約：元の同型を選び直さない。使われ方：共同実現同型の添字制限。 -/
lemma functorIsoCurry_precompose_first {A A' B X : SSet.{u}} [Quasicategory X]
    (q : A' ⟶ A) {f g : A ⊗ B ⟶ X} (e : FunctorIso f g) :
    diagramIsoCongr (curry_pre_app q f).symm (curry_pre_app q g).symm
      (FunctorIso.curry (e.precomp (q ▷ B))) = e.curry.postcomp ((pre q).app X) := by
  apply Iso.ext
  rw [diagramIsoCongr_hom, functorIsoCurry_hom, functorIsoPrecomp_hom,
    functorIsoPostcomp_hom, functorIsoCurry_hom]
  exact curryFunctorHom_precompose_first q e.hom

/-- 概要：図式等式による指定同型の移送は元の全関手での後合成と両立する。
方針：二つの図式等式を消去する。
規約：元の同型を保持する。使われ方：添字制限後の実現比較の端点正規化。 -/
lemma diagramIsoCongr_postcomp {A X Y : SSet.{u}} (q : X ⟶ Y)
    {f g f' g' : A ⟶ X} (hf : f = f') (hg : g = g') (e : FunctorIso f g) :
    (diagramIsoCongr hf hg e).postcomp q =
      diagramIsoCongr (congrArg (fun h ↦ h ≫ q) hf) (congrArg (fun h ↦ h ≫ q) hg)
        (e.postcomp q) := by
  subst f' g'
  simp only [diagramIsoCongr, eqToIso_refl, Iso.refl_symm, Iso.refl_trans, Iso.trans_refl]

end SerrePositivity.InfinityCategories.F2.Presentable
