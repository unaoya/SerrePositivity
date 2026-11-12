module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitFullyFaithful

/-! # 普遍余錐間のホモトピー圏の射の一意な持ち上げ

概要：図式のホモトピー圏の射は、指定された普遍余錐間の射に一意に持ち上がる。
方針：図式への射影の充満忠実性の Hom の逆写像を使う。
規約：対象は既に存在する普遍余錐であり、全図式での余極限の存在を仮定しない。
使われ方：S4 の余極限間の射の選択の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：指定された普遍余錐間に図式の h の射を持ち上げる。
方針：射影の充満忠実性による Hom の逆写像を使う。
規約：基底の射は射影された二対象の間。使われ方：余極限間の比較射。 -/
def colimitCoconeLiftHom {K X : SSet.{u}} [Quasicategory X]
    {a b : hoFunctor.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitCocones K X)}
    (f : (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitCoconeProjection K X)).toFunctor.obj a ⟶
      (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitCoconeProjection K X)).toFunctor.obj b) : a ⟶ b :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitCoconeProjectionHoFullyFaithful K X).preimage f

/-- 概要：持ち上げた射を図式へ射影すると元の射に戻る。
方針：Hom の逆写像の右逆則。
規約：h の射の厳密な等式。使われ方：持ち上げの比較。 -/
lemma colimitCoconeProjection_map_liftHom {K X : SSet.{u}} [Quasicategory X]
    {a b : hoFunctor.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitCocones K X)}
    (f : (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitCoconeProjection K X)).toFunctor.obj a ⟶
      (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitCoconeProjection K X)).toFunctor.obj b) :
    (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitCoconeProjection K X)).toFunctor.map (colimitCoconeLiftHom f) = f :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitCoconeProjectionHoFullyFaithful K X).map_preimage f

/-- 概要：持ち上げは図式への射影の値によって一意に決まる。
方針：忠実性で像の等式を反映する。
規約：同じ二つの普遍余錐間の射。使われ方：実際の辺による持ち上げとの照合。 -/
lemma colimitCoconeLiftHom_unique {K X : SSet.{u}} [Quasicategory X]
    {a b : hoFunctor.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitCocones K X)}
    (f : (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitCoconeProjection K X)).toFunctor.obj a ⟶
      (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitCoconeProjection K X)).toFunctor.obj b)
    (g : a ⟶ b) (hg : (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitCoconeProjection K X)).toFunctor.map g = f) :
    g = colimitCoconeLiftHom f :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitCoconeProjection_ho_map_injective (hg.trans (colimitCoconeProjection_map_liftHom f).symm)

/-- 概要：恒等射の持ち上げは恒等射。
方針：充満忠実関手の逆写像の恒等則。
規約：普遍余錐の対象は任意。使われ方：余極限の関手性。 -/
lemma colimitCoconeLiftHom_id {K X : SSet.{u}} [Quasicategory X]
    (a : hoFunctor.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitCocones K X)) :
    colimitCoconeLiftHom (𝟙 ((hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitCoconeProjection K X)).toFunctor.obj a)) =
      𝟙 a :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitCoconeProjectionHoFullyFaithful K X).preimage_id

/-- 概要：合成の持ち上げは持ち上げた射の合成。
方針：充満忠実関手の逆写像の合成則。
規約：同じ中間の普遍余錐を指定する。使われ方：余極限の関手性。 -/
lemma colimitCoconeLiftHom_comp {K X : SSet.{u}} [Quasicategory X]
    {a b c : hoFunctor.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitCocones K X)}
    (f : (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitCoconeProjection K X)).toFunctor.obj a ⟶
      (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitCoconeProjection K X)).toFunctor.obj b)
    (g : (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitCoconeProjection K X)).toFunctor.obj b ⟶
      (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitCoconeProjection K X)).toFunctor.obj c) :
    colimitCoconeLiftHom (f ≫ g) = colimitCoconeLiftHom f ≫ colimitCoconeLiftHom g :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitCoconeProjectionHoFullyFaithful K X).preimage_comp f g

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
