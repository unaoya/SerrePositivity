module

public import SerrePositivity.InfinityCategories.Sheaves.SheafCondition
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableSmallLimits

/-!
概要：小さい通常site上の前層の大域切断を、同じ指定極限錐の頂点として定める。
方針：presentable係数の小極限の存在を使う。
使われ方：HTT 5.5.2.4、Kerodon §7.1（Tag 02H1）、層化後のRΓの入口。
規約：層化前のΓを定める。RΓとの比較は指定単位を用いて後続で示す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Sheaves
variable {𝒞 : Type u} [SmallCategory 𝒞] {E : SSet.{u+1}} [Quasicategory E]

/-- 概要：前層 F の大域切断の錐：添字全体の上の極限錐。
方針：`HasLimit F` から錐を選ぶ。
規約：選択を含む。頂点の等号は主張しない。
使われ方：`globalSections`。 -/
def globalSectionsCone (F : Presheaf 𝒞 E) (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit F) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone F :=
  h.choose

lemma globalSectionsCone_isLimit (F : Presheaf 𝒞 E) (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit F) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (globalSectionsCone F h) :=
  h.choose_spec

/-- 概要：大域切断 Γ(F) = lim_{N(𝒞)^op} F。
方針：選んだ極限錐の頂点。
規約：E の頂点。
使われ方：RΓ の定義。Mathlib の 1 圏版は `Sheaf.ΓNatIsoLim`。 -/
def globalSections (F : Presheaf 𝒞 E) (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit F) : E _⦋0⦌ :=
  (globalSectionsCone F h).vertex

/-- 概要：E が presentable なら任意の前層が大域切断を持つ。
方針：`IsPresentable.hasLimit`（形状 `nerve 𝒞ᵒᵖ : SSet.{u}` を持ち上げたもの）。
規約：𝒞 が小さいことを使う。
使われ方：Γ の存在。 -/
lemma hasLimit_presheaf (hE : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) (F : Presheaf 𝒞 E) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit F :=
  hE.hasLimit F


end SerrePositivity.InfinityCategories.Sheaves
