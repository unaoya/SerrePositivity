module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.JointComparisonPrecomposition

/-!
概要：指定 Hom と指定同型の curry は第二変数の前合成と両立する。
方針：関手空間の二つの厳密な合成写像を同定し、端点移送を正規化する。
規約：元の射・同型・前合成関手を保持する。
使われ方：P-12 の共同比較の実現と指定同型の前合成の照合。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：全関手空間の curry は第二変数の前合成と厳密に可換。
方針：全次数の関手単体を二重評価して同じ作用を得る。
規約：quasicategory 性を要求しない。使われ方：指定 Hom の前合成の比較。 -/
lemma functorSpaceCurryMap_precompose_second {A B B' X : SSet.{u}} (q : B' ⟶ B) :
    (pre (A ◁ q)).app X ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorSpaceCurryMap A B' X =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorSpaceCurryMap A B X ≫ (pre q).app ((ihom A).obj X) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro f
  apply CategoryTheory.Functor.functorHom_ext
  intro m α
  apply ConcreteCategory.hom_ext
  intro b
  apply CategoryTheory.Functor.functorHom_ext
  intro k β
  apply ConcreteCategory.hom_ext
  intro a
  have h := ConcreteCategory.congr_hom (q.naturality β) b
  exact congrArg (fun z ↦ f.app k (α ≫ β) (a, z)) h

/-- 概要：正規化 Hom の端点移送は同じ全 Hom 作用の端点等式の合成。
方針：二つの図式等式を消去して恒等の共役を除く。
規約：元の Hom を保持する。使われ方：curry の前合成公式の端点正規化。 -/
lemma kanFunctorHomCongr_normalizedMap {A X Z : SSet.{u}}
    (t : Z ⟶ (ihom A).obj X) {x y : Z _⦋0⦌} {f g f' g' : A ⟶ X}
    (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f = t.app (Opposite.op ⦋0⦌) x)
    (hy : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g = t.app (Opposite.op ⦋0⦌) y)
    (hf : f = f') (hg : g = g')
    (α : (HomotopyCategory.mk x : hoFunctor.obj Z) ⟶ HomotopyCategory.mk y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr hf hg (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.normalizedVertexHomMap t hx hy α) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.normalizedVertexHomMap t ((congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex hf).symm.trans hx)
        ((congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex hg).symm.trans hy) α := by
  subst f' g'
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr, Iso.homCongr_apply, eqToIso_refl,
    Iso.refl_inv, Iso.refl_hom, Category.id_comp, Category.comp_id]

/-- 概要：指定 Hom の curry は元の第二変数の前合成と両立する。
方針：二つの正規化 Hom 作用を厳密に可換な関手空間の写像へ戻す。
規約：元の指定射と元の図式等式を保持する。使われ方：指定同型の実現の前合成。 -/
lemma curryFunctorHom_precompose_second {A B B' X : SSet.{u}} (q : B' ⟶ B)
    {f g : A ⊗ B ⟶ X} (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f g) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr (curry_natural_left q f) (curry_natural_left q g)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.curryFunctorHom (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.precomposeFunctorHom (A ◁ q) α)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.precomposeFunctorHom q (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.curryFunctorHom α) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.curryFunctorHom_eq_normalizedMap]
  rw [kanFunctorHomCongr_normalizedMap]
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.precomposeFunctorHom
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.normalizedVertexHomMap_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.normalizedVertexHomMap_comp]
  have hm : HEq
      ((hoFunctor.map ((pre (A ◁ q)).app X ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorSpaceCurryMap A B' X)).toFunctor.map α)
      ((hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorSpaceCurryMap A B X ≫
        (pre q).app ((ihom A).obj X))).toFunctor.map α) := by
    rw [functorSpaceCurryMap_precompose_second]
  exact eq_of_heq ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.normalizedVertexHomMap_heq _ _ _ α).trans
    (hm.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.normalizedVertexHomMap_heq _ _ _ α).symm))

/-- 概要：指定同型の curry は第二変数の前合成と両立する。
方針：順方向の Hom の curry と前合成の同定を使う。
規約：元の同型を保持する。使われ方：共同比較の実現前後の前合成の照合。 -/
lemma functorIsoCurry_precompose_second {A B B' X : SSet.{u}} [Quasicategory X]
    (q : B' ⟶ B) {f g : A ⊗ B ⟶ X} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.diagramIsoCongr (curry_natural_left q f) (curry_natural_left q g)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorIso.curry (e.precomp (A ◁ q))) = e.curry.precomp q := by
  apply Iso.ext
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.diagramIsoCongr_hom, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorIsoCurry_hom, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorIsoPrecomp_hom,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorIsoPrecomp_hom, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorIsoCurry_hom]
  exact curryFunctorHom_precompose_second q e.hom

/-- 概要：同型の図式等式による移送を二回行うと、合成した等式での移送となる。
方針：四つの端点等式を消去する。
規約：元の同型を保持する。使われ方：実現比較の端点移送の合成。 -/
lemma diagramIsoCongr_comp {A X : SSet.{u}} {f g f' g' f'' g'' : A ⟶ X}
    (hf : f = f') (hg : g = g') (hf' : f' = f'') (hg' : g' = g'')
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.diagramIsoCongr hf' hg' (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.diagramIsoCongr hf hg e) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.diagramIsoCongr (hf.trans hf') (hg.trans hg') e := by
  subst f' g' f'' g''
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.diagramIsoCongr, eqToIso_refl, Iso.refl_symm, Iso.refl_trans, Iso.trans_refl]

/-- 概要：curry は元の図式等式による指定同型の移送と両立する。
方針：二つの図式等式を消去する。
規約：元の同型を保持する。使われ方：共同比較同型の前合成の正規化。 -/
lemma diagramIsoCongr_curry {A B X : SSet.{u}} [Quasicategory X]
    {f g f' g' : A ⊗ B ⟶ X} (hf : f = f') (hg : g = g') (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorIso.curry (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.diagramIsoCongr hf hg e) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.diagramIsoCongr (congrArg curry hf) (congrArg curry hg) e.curry := by
  subst f' g'
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.diagramIsoCongr, eqToIso_refl, Iso.refl_symm, Iso.refl_trans, Iso.trans_refl]

/-- 概要：指定同型の端点移送は元の関手の前合成と両立する。
方針：二つの図式等式を消去する。
規約：元の同型を保持する。使われ方：実現比較の前合成後の端点正規化。 -/
lemma diagramIsoCongr_precomp {A B X : SSet.{u}} (q : B ⟶ A)
    {f g f' g' : A ⟶ X} (hf : f = f') (hg : g = g') (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.diagramIsoCongr hf hg e).precomp q =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.diagramIsoCongr (congrArg (fun h ↦ q ≫ h) hf) (congrArg (fun h ↦ q ≫ h) hg)
        (e.precomp q) := by
  subst f' g'
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.diagramIsoCongr, eqToIso_refl, Iso.refl_symm, Iso.refl_trans, Iso.trans_refl]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
