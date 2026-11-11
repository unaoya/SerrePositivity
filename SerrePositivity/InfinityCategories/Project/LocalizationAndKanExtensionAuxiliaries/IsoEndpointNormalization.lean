module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorIsoPointEvaluation

/-!
概要：指定同型の両端の補正は関手による指定像と合成に整合する。
方針：明示した対象の等式を消去し、中間の補正が相殺する式を証明する。
規約：端点の等式を入力として保持。使われ方：native path の像と左右の fiber 同型の合成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v u' v'
open CategoryTheory
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries

/-- 対象の明示した等式だけで指定同型の両端を揃える。 -/
def isoNormalizeEndpoints {C : Type u} [Category.{v} C] {a b a' b' : C}
    (e : a ≅ b) (ha : a = a') (hb : b = b') : a' ≅ b' :=
  (eqToIso ha).symm ≪≫ e ≪≫ eqToIso hb

/-- 両端の補正を関手へ写すと、同じ指定像の両端の補正になる。 -/
lemma isoNormalizeEndpoints_map {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (F : C ⥤ D) {a b a' b' : C}
    (e : a ≅ b) (ha : a = a') (hb : b = b') :
    F.mapIso (isoNormalizeEndpoints e ha hb) =
      isoNormalizeEndpoints (F.mapIso e) (congrArg F.obj ha) (congrArg F.obj hb) := by
  subst a' b'
  simp only [isoNormalizeEndpoints, eqToIso_refl, Iso.refl_symm, Iso.refl_trans, Iso.trans_refl]

/-- 明示した両端の補正は関手による指定像の値を HEq で保持する。 -/
lemma isoNormalizeEndpoints_map_heq {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (F : C ⥤ D) {a b a' b' : C}
    (e : a ≅ b) (ha : a = a') (hb : b = b') :
    HEq (F.mapIso (isoNormalizeEndpoints e ha hb)) (F.mapIso e) := by
  subst a' b'
  simp only [isoNormalizeEndpoints, eqToIso_refl, Iso.refl_symm, Iso.refl_trans, Iso.trans_refl]
  rfl

/-- 左右の指定同型を共通対象で合成すると、中間の両端補正は相殺する。 -/
lemma isoNormalizeEndpoints_span {C : Type u} [Category.{v} C]
    {a b l r a' b' l' r' : C} (e : a ≅ l) (f : b ≅ r)
    (h : a = b) (ha : a = a') (hb : b = b') (hl : l = l') (hr : r = r')
    (h' : a' = b') :
    (isoNormalizeEndpoints e ha hl).symm ≪≫ eqToIso h' ≪≫
      isoNormalizeEndpoints f hb hr =
    isoNormalizeEndpoints (e.symm ≪≫ eqToIso h ≪≫ f) hl hr := by
  subst a' b' l' r' b
  simp only [isoNormalizeEndpoints, eqToIso_refl, Iso.refl_symm, Iso.refl_trans, Iso.trans_refl]

/-- 二段の端点補正は、対象の等式を合成した一段の補正に等しい。 -/
lemma isoNormalizeEndpoints_trans {C : Type u} [Category.{v} C]
    {a b a' b' a'' b'' : C} (e : a ≅ b)
    (ha : a = a') (hb : b = b') (ha' : a' = a'') (hb' : b' = b'') :
    isoNormalizeEndpoints (isoNormalizeEndpoints e ha hb) ha' hb' =
      isoNormalizeEndpoints e (ha.trans ha') (hb.trans hb') := by
  subst a' b' a'' b''
  simp only [isoNormalizeEndpoints, eqToIso_refl, Iso.refl_symm, Iso.refl_trans, Iso.trans_refl]

/-- 共通対象を等式で揃えた左右の指定同型の合成を、関手が同じ指定合成へ写す。 -/
lemma functor_mapIso_span {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (F : C ⥤ D)
    {a b l r : C} (e : a ≅ l) (f : b ≅ r) (h : a = b) :
    F.mapIso (e.symm ≪≫ eqToIso h ≪≫ f) =
      (F.mapIso e).symm ≪≫ eqToIso (congrArg F.obj h) ≪≫ F.mapIso f := by
  subst b
  simp only [eqToIso_refl, Iso.refl_trans, Functor.mapIso_trans, Functor.mapIso_symm]

/-- 明示した端点等式で指定同型を補正すると、同じ値の指定同型へ厳密に一致する。 -/
lemma isoNormalizeEndpoints_eq_of_heq {C : Type u} [Category.{v} C]
    {a b a' b' : C} (e : a ≅ b) (e' : a' ≅ b') (ha : a = a') (hb : b = b')
    (he : HEq e e') : isoNormalizeEndpoints e ha hb = e' := by
  exact eq_of_heq ((_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.iso_endpoints_heq e ha hb).trans he)

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries
