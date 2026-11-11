module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.AdjointHomOne

/-!
概要：元の Hom の端点輸送と関手作用・随伴 Hom₁ 対応の両立。
方針：端点の等式を帰納法で除き、同じ射の表示へ戻す。
規約：移す始域・標的の関手を全て明示する。
使われ方：転置したパラメータ自然性の端点輸送の計算。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：始点の関手の等式だけで元の Hom の型を輸送する。
方針：FunctorHom の型の等式による cast の全単射を使う。
規約：始点だけを変え、終点は保持する。
使われ方：転置した始点の正規化を大きな恒等射の合成へ展開しない界面。 -/
def functorHomSourceEquiv {A E : SSet.{u}} {U U' V : A ⟶ E} (h : U = U') :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom U V ≃ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom U' V :=
  Equiv.cast (congrArg (fun T ↦ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom T V) h)

/-- 概要：始点の型輸送は Hom の合成を保つ。
方針：始点の等式を除き恒等 cast を計算する。
規約：中間点・終点は保持する。
使われ方：前合成の入口の合成保存。 -/
lemma functorHomSourceEquiv_comp {A E : SSet.{u}} {U U' V W : A ⟶ E}
    (h : U = U') (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom U V) (β : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom V W) :
    functorHomSourceEquiv h (α ≫ β) = functorHomSourceEquiv h α ≫ β := by
  subst U'
  rfl

/-- 概要：始点の型輸送と両端の同型による輸送を合成の二因子で比較する。
方針：二つの関手の等式を除き恒等輸送を相殺する。
規約：終点の関手は変更しない。
使われ方：前合成の入口の始域自然性。 -/
lemma functorHomSourceEquiv_factor {A E : SSet.{u}} {U U' V V' W : A ⟶ E}
    (hU : U = U') (hV : V = V') (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom U V) (β : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom V W) :
    functorHomSourceEquiv hU (α ≫ β) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr hU hV α ≫ functorHomSourceEquiv hV β := by
  subst U'
  subst V'
  simp only [functorHomSourceEquiv, Equiv.cast_refl, Equiv.refl_apply,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr, Iso.homCongr_apply, eqToIso.inv, eqToIso.hom,
    eqToHom_refl, Category.id_comp, Category.comp_id]

/-- 概要：始点の型輸送は始点だけの同型輸送と同じ元の Hom を与える。
方針：始点の等式を除き恒等輸送を計算する。
規約：同じ端点と射を保持する。
使われ方：既存の両端輸送による自然性との接続。 -/
lemma functorHomSourceEquiv_eq_congr {A E : SSet.{u}} {U U' V : A ⟶ E}
    (h : U = U') (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom U V) :
    functorHomSourceEquiv h α = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr h rfl α := by
  subst U'
  simp only [functorHomSourceEquiv, Equiv.cast_refl, Equiv.refl_apply,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr, Iso.homCongr_apply, eqToIso.inv, eqToIso.hom,
    eqToHom_refl, Category.id_comp, Category.comp_id]

/-- 概要：恒等の端点輸送は元の Hom を保つ。
方針：恒等同型による共役を相殺する。
規約：関手圏の内部構成は展開しない。
使われ方：転置の合成保存の恒等端点の簡約。 -/
lemma functorHomCongr_refl {A E : SSet.{u}} {U V : A ⟶ E} (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom U V) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr (U := U) (V := V) rfl rfl α = α := by
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr, Iso.homCongr_apply, eqToIso.inv, eqToIso.hom,
    eqToHom_refl, Category.id_comp, Category.comp_id]

/-- 概要：始点だけの輸送は合成の第二射を保持する。
方針：始点の等式を除き恒等輸送を計算する。
規約：中間点・終点は変更しない。
使われ方：前合成の入口の合成保存。 -/
lemma functorHomCongr_source_comp {A E : SSet.{u}} {U U' V W : A ⟶ E}
    (hU : U = U') (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom U V) (β : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom V W) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr hU rfl (α ≫ β) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr hU rfl α ≫ β := by
  subst U'
  simp only [functorHomCongr_refl]

/-- 概要：端点輸送を二回行うと等式の連結による輸送になる。
方針：端点の等式を除き恒等輸送を計算する。
規約：元の Hom を保持する。
使われ方：転置の二つの正規化の比較。 -/
lemma functorHomCongr_trans {A E : SSet.{u}}
    {U V U' V' U'' V'' : A ⟶ E}
    (hU : U = U') (hV : V = V') (hU' : U' = U'') (hV' : V' = V'')
    (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom U V) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr hU' hV' (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr hU hV α) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr (hU.trans hU') (hV.trans hV') α := by
  subst U'
  subst V'
  subst U''
  subst V''
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr, Iso.homCongr_apply, eqToIso.inv, eqToIso.hom,
    eqToHom_refl, Category.id_comp, Category.comp_id]

/-- 概要：端点輸送は関手による後合成の Hom 作用と可換。
方針：二つの端点の等式を除き恒等輸送を計算する。
規約：充填性の仮定は不要。
使われ方：転置後のパラメータ自然性。 -/
lemma functorHomCongr_postcomp {A E E' : SSet.{u}} (k : E ⟶ E')
    {U V U' V' : A ⟶ E} (hU : U = U') (hV : V = V') (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom U V) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr (congrArg (· ≫ k) hU) (congrArg (· ≫ k) hV)
      ((hoFunctor.map ((ihom A).map k)).toFunctor.map α) =
    (hoFunctor.map ((ihom A).map k)).toFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr hU hV α) := by
  subst U'
  subst V'
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr, Iso.homCongr_apply, eqToIso.inv, eqToIso.hom,
    eqToHom_refl, Category.id_comp, Category.comp_id]

/-- 概要：端点輸送は随伴の Hom₁ の逆対応と可換。
方針：二つの端点の等式を除き恒等輸送を相殺する。
規約：元の左・右随伴を保持する。
使われ方：転置されたパラメータの関手を正規化する。 -/
lemma adjointHomOneEquiv_congr {C D E : SSet.{u}}
    [Quasicategory C] [Quasicategory D] [Quasicategory E]
    {L : C ⟶ D} {R : D ⟶ C} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction L R)
    {U U' : C ⟶ E} {V V' : D ⟶ E} (hU : U = U') (hV : V = V')
    (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (R ≫ U) V) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr hU (congrArg (L ≫ ·) hV) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.adjointHomOneEquiv a U V α) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.adjointHomOneEquiv a U' V'
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr (congrArg (R ≫ ·) hU) hV α) := by
  subst U'
  subst V'
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr, Iso.homCongr_apply, eqToIso.inv, eqToIso.hom,
    eqToHom_refl, Category.id_comp, Category.comp_id]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
