module

public import SerrePositivity.InfinityCategories.F2.Presentable.Duality.AdjointHomOne

/-!
概要：元の Hom の端点輸送と関手作用・随伴 Hom₁ 対応の両立。
方針：端点の等式を帰納法で除き、同じ射の表示へ戻す。
規約：移す始域・標的の関手を全て明示する。
使われ方：転置したパラメータ自然性の端点輸送の計算。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable.Duality

/-- 概要：恒等の端点輸送は元の Hom を保つ。
方針：恒等同型による共役を相殺する。
規約：関手圏の内部構成は展開しない。
使われ方：転置の合成保存の恒等端点の簡約。 -/
lemma functorHomCongr_refl {A E : SSet.{u}} {U V : A ⟶ E} (α : FunctorHom U V) :
    F1B.kanFunctorHomCongr (U := U) (V := V) rfl rfl α = α := by
  simp only [F1B.kanFunctorHomCongr, Iso.homCongr_apply, eqToIso.inv, eqToIso.hom,
    eqToHom_refl, Category.id_comp, Category.comp_id]

/-- 概要：始点だけの輸送は合成の第二射を保持する。
方針：始点の等式を除き恒等輸送を計算する。
規約：中間点・終点は変更しない。
使われ方：前合成の入口の合成保存。 -/
lemma functorHomCongr_source_comp {A E : SSet.{u}} {U U' V W : A ⟶ E}
    (hU : U = U') (α : FunctorHom U V) (β : FunctorHom V W) :
    F1B.kanFunctorHomCongr hU rfl (α ≫ β) =
      F1B.kanFunctorHomCongr hU rfl α ≫ β := by
  subst U'
  simp only [functorHomCongr_refl]

/-- 概要：端点輸送を二回行うと等式の連結による輸送になる。
方針：端点の等式を除き恒等輸送を計算する。
規約：元の Hom を保持する。
使われ方：転置の二つの正規化の比較。 -/
lemma functorHomCongr_trans {A E : SSet.{u}}
    {U V U' V' U'' V'' : A ⟶ E}
    (hU : U = U') (hV : V = V') (hU' : U' = U'') (hV' : V' = V'')
    (α : FunctorHom U V) :
    F1B.kanFunctorHomCongr hU' hV' (F1B.kanFunctorHomCongr hU hV α) =
      F1B.kanFunctorHomCongr (hU.trans hU') (hV.trans hV') α := by
  subst U'
  subst V'
  subst U''
  subst V''
  simp only [F1B.kanFunctorHomCongr, Iso.homCongr_apply, eqToIso.inv, eqToIso.hom,
    eqToHom_refl, Category.id_comp, Category.comp_id]

/-- 概要：端点輸送は関手による後合成の Hom 作用と可換。
方針：二つの端点の等式を除き恒等輸送を計算する。
規約：充填性の仮定は不要。
使われ方：転置後のパラメータ自然性。 -/
lemma functorHomCongr_postcomp {A E E' : SSet.{u}} (k : E ⟶ E')
    {U V U' V' : A ⟶ E} (hU : U = U') (hV : V = V') (α : FunctorHom U V) :
    F1B.kanFunctorHomCongr (congrArg (· ≫ k) hU) (congrArg (· ≫ k) hV)
      ((hoFunctor.map ((ihom A).map k)).toFunctor.map α) =
    (hoFunctor.map ((ihom A).map k)).toFunctor.map (F1B.kanFunctorHomCongr hU hV α) := by
  subst U'
  subst V'
  simp only [F1B.kanFunctorHomCongr, Iso.homCongr_apply, eqToIso.inv, eqToIso.hom,
    eqToHom_refl, Category.id_comp, Category.comp_id]

/-- 概要：端点輸送は随伴の Hom₁ の逆対応と可換。
方針：二つの端点の等式を除き恒等輸送を相殺する。
規約：元の左・右随伴を保持する。
使われ方：転置されたパラメータの関手を正規化する。 -/
lemma adjointHomOneEquiv_congr {C D E : SSet.{u}}
    [Quasicategory C] [Quasicategory D] [Quasicategory E]
    {L : C ⟶ D} {R : D ⟶ C} (a : QCatAdjunction L R)
    {U U' : C ⟶ E} {V V' : D ⟶ E} (hU : U = U') (hV : V = V')
    (α : FunctorHom (R ≫ U) V) :
    F1B.kanFunctorHomCongr hU (congrArg (L ≫ ·) hV) (adjointHomOneEquiv a U V α) =
      adjointHomOneEquiv a U' V'
        (F1B.kanFunctorHomCongr (congrArg (R ≫ ·) hU) hV α) := by
  subst U'
  subst V'
  simp only [F1B.kanFunctorHomCongr, Iso.homCongr_apply, eqToIso.inv, eqToIso.hom,
    eqToHom_refl, Category.id_comp, Category.comp_id]

end SerrePositivity.InfinityCategories.F2.Presentable.Duality
