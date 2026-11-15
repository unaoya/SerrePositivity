module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeJoinRightHom
public import Mathlib.CategoryTheory.Comma.Arrow

/-!
概要：両端の表示を変えた関手間の射は、Arrow の対象として元の射に等しい。
方針：端点の等式による二つの輸送を Arrow 上で相殺する。
使われ方：Kerodon §7.3（Tag 02Y1）、HTT 6.2.2.6 の指定余単位の制限。
規約：代表の端点が定義上同じであることを要求しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 端点の等式に沿って移した射の Arrow の対象は、元の対象と同じ。 -/
lemma kanFunctorHomCongr_arrow {A D : SSet.{u}} {U V U' V' : A ⟶ D}
    (hU : U = U') (hV : V = V') (α : FunctorHom U V) :
    Arrow.mk (kanFunctorHomCongr hU hV α) = Arrow.mk α := by
  simp only [kanFunctorHomCongr, Iso.homCongr_apply, eqToIso.inv, eqToIso.hom,
    Arrow.arrow_mk_comp_eqToHom, Arrow.arrow_mk_eqToHom_comp]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
