module

public import SerrePositivity.InfinityCategories.HomotopyLimits.WeightedConeRestriction

/-!
概要：豊穣 Hom で計算する strict な homotopy 極限を coherent nerve の極限錐へ移す。
方針：反転した Bousfield–Kan 比較の同値性を主可換式と native な極限判定に渡す。
規約：局所 Kan な単体的圏で、離散図式・一脚 fibration の cospan・fibration の塔を扱う。
使われ方：HTT 4.2.4.1 の双対の限定形、Kerodon 7.5.3.12、7.5.4.6。𝒮・Sp への共有界面。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
namespace SerrePositivity.InfinityCategories.HomotopyLimits

variable {C : Type v} [Category.{u} C] [SimplicialCategory C]
  [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]

/-- 概要：各豊穣 Hom が積の錐である strict な錐は coherent nerve の積の錐となる。
方針：離散図式の q′ の比較の同値性を主極限判定に渡す。
規約：積の添字 J に有限性・非空性は要求しない。
使われ方：HTT 4.2.4.1 の双対、Kerodon 7.5.4.6 の豊穣積から ∞ 積への移送。 -/
lemma strictCoherentCone_isLimit_of_discrete_homLimit {J : Type u}
    {F : Discrete J ⥤ C} (c : Cone F) (hc : ∀ x : C, IsLimit (simplicialHomCone c x)) :
    IsLimitCone (strictCoherentCone c) := by
  apply (strictCoherentCone_isLimit_iff_reflectedStrictConeSectionsComparison c).mpr
  intro x
  exact reflectedStrictConeSectionsComparison_discrete_homotopyEquivalence c x (hc x)

/-- 概要：各豊穣 Hom で一脚 fibration の引き戻しとなる strict な錐は ∞ 引き戻しの錐となる。
方針：cospan の q′ の比較の同値性を主可換式と native な極限判定で移す。
規約：Hom 錐の極限性と左脚の fibration 性を全 x で要求し、右脚は任意。
使われ方：HTT 4.2.4.1 の双対、Kerodon 7.5.3.12、7.5.4.6 の引き戻しの移送。 -/
lemma strictCoherentCone_isLimit_of_cospan_homLimit
    {F : AsSmall.{u} WalkingCospan ⥤ C} (c : Cone F)
    (hc : ∀ x : C, IsLimit (simplicialHomCone c x))
    [∀ x : C, Fibration
      ((simplicialHomDiagram F x).map (AsSmall.up.map WalkingCospan.Hom.inl))] :
    IsLimitCone (strictCoherentCone c) := by
  apply (strictCoherentCone_isLimit_iff_reflectedStrictConeSectionsComparison c).mpr
  intro x
  exact reflectedStrictConeSectionsComparison_cospan_homotopyEquivalence c x (hc x)

/-- 概要：各豊穣 Hom で fibration の塔の極限となる strict な錐は ∞ 極限錐となる。
方針：塔の q′ の比較の同値性を主可換式と native な極限判定で移す。
規約：全 x で Hom 錐の極限性と全隣接遷移の fibration 性を要求する。
使われ方：HTT 4.2.4.1 の双対、Kerodon 7.5.3.12、7.5.4.6 の塔の極限の移送。 -/
lemma strictCoherentCone_isLimit_of_tower_homLimit
    {F : AsSmall.{u} ℕᵒᵖ ⥤ C} (c : Cone F)
    (hc : ∀ x : C, IsLimit (simplicialHomCone c x))
    [∀ (x : C) (n : ℕ), Fibration
      ((simplicialHomDiagram F x).map (AsSmall.up.map (homOfLE (Nat.le_succ n)).op))] :
    IsLimitCone (strictCoherentCone c) := by
  apply (strictCoherentCone_isLimit_iff_reflectedStrictConeSectionsComparison c).mpr
  intro x
  exact reflectedStrictConeSectionsComparison_tower_homotopyEquivalence c x (hc x)

end SerrePositivity.InfinityCategories.HomotopyLimits
