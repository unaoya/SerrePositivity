module

public import SerrePositivity.InfinityCategories.HomotopyLimits.StrictConeSimplex
public import SerrePositivity.InfinityCategories.Core.JoinCurryHomExt
public import SerrePositivity.InfinityCategories.Core.SliceRestriction
public import SerrePositivity.InfinityCategories.Core.TerminalMap

/-!
概要：strict な coherent 錐の構成は通常の関手による添字の制限と厳密に可換。
方針：添字の全標準単体上の式を比較し、同型による制限では slice の同型で極限性を移す。
規約：同じ宇宙の二つの小圏を扱い、図式の等式で移送を明示する。
使われ方：HTT 4.2.4.1、Kerodon 7.5.4.6、逐次余極限の反対の塔への再添字。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

/-- 概要：native な錐を添字の射に沿って制限する。
方針：slice の制限写像を零単体に適用する。
規約：添字の射は任意。
使われ方：Kerodon 7.5.4.6、反対の添字の表示を標準の形へ移す。 -/
def coherentConeRestrict {K L X : SSet.{u}} {p : K ⟶ X} (c : JoinCone p) (f : L ⟶ K) :
    JoinCone (f ≫ p) :=
  (sliceOverRestrict p f).app (Opposite.op ⦋0⦌) c

/-- 概要：添字の同型に沿った錐の制限は native な極限性を保ち反映する。
方針：slice の制限の同型による終対象性の不変性を使う。
規約：値域の quasicategory 性を要求しない。
使われ方：Kerodon 7.5.4.6、標準の添字への書き換えでの極限判定。 -/
lemma coherentConeRestrict_isLimit_iff {K L X : SSet.{u}} {p : K ⟶ X}
    (c : JoinCone p) (f : L ⟶ K) [IsIso f] :
    IsLimitCone c ↔ IsLimitCone (coherentConeRestrict c f) := by
  have := sliceOverRestrict_isIso p f
  constructor
  · exact fun h ↦ h.map_of_isIso (sliceOverRestrict p f)
  · exact fun h ↦ isTerminalVertex_of_trivialKanFibration (sliceOverRestrict p f) h

/-- 概要：図式の等式で錐を移送しても native な極限性は変わらない。
方針：図式の等式を除き、固定条件の証明の無関係性を使う。
規約：JoinCone.cast に対する両向きの判定。
使われ方：Kerodon 7.5.4.6、再添字した strict な図式の正規化。 -/
lemma coherentConeCast_isLimit_iff {K X : SSet.{u}} {p q : K ⟶ X}
    (c : JoinCone p) (h : p = q) : IsLimitCone (c.cast h) ↔ IsLimitCone c := by
  subst q
  rfl

variable {I J : Type u} [SmallCategory I] [SmallCategory J]
  {C : Type v} [Category.{u} C] [SimplicialCategory C]

/-- 概要：通常の関手による錐の制限は coherent 表示の join の前合成に一致する。
方針：固定頂点と右因子の全標準単体で比較し、前置した射列の同じ値を計算する。
規約：G の同値性や局所 Kan 性を要求しない。
使われ方：HTT 4.2.4.1、Kerodon 7.5.4.6、反対の添字を標準形へ移す主可換式。 -/
lemma strictCoherentConeMap_whisker {F : I ⥤ C} (c : Cone F) (G : J ⥤ I) :
    joinMap (𝟙 (Δ[0] : SSet.{max u v}))
        ((SSet.uliftFunctor.{v, u}).map (nerveMap G)) ≫ strictCoherentConeMap c =
      strictCoherentConeMap (c.whisker G) := by
  apply join_right_hom_ext
  · rw [← Category.assoc, joinInl_joinMap, Category.id_comp,
      strictCoherentConeMap_inl, strictCoherentConeMap_inl]
    rfl
  · intro n a
    rw [← Category.assoc, ← joinMap_comp, Category.id_comp,
      strictCoherentConeMap_simplex, strictCoherentConeMap_simplex]
    rw [SSet.yonedaEquiv_comp]
    rfl

/-- 概要：再添字した通常の錐の coherent 表示は元の native な錐の制限を移送したもの。
方針：join からの写像の主可換式を固定図式の等式で部分型へ戻す。
規約：strictCoherentDiagram_precomp による移送を明示する。
使われ方：Kerodon 7.5.4.6、通常の添字の変更と native な極限性を結ぶ。 -/
lemma strictCoherentCone_whisker {F : I ⥤ C} (c : Cone F) (G : J ⥤ I) :
    strictCoherentCone (c.whisker G) =
      (coherentConeRestrict (strictCoherentCone c)
        ((SSet.uliftFunctor.{v, u}).map (nerveMap G))).cast
          (strictCoherentDiagram_precomp G F) := by
  apply Subtype.ext
  exact (strictCoherentConeMap_whisker c G).symm

/-- 概要：nerve の持ち上げが同型な再添字は strict な錐の native な極限性を保ち反映する。
方針：通常の錐の再添字の等式、図式の移送、slice の制限の同型を合成する。
規約：通常の関手の圏同値性だけで同型性を代用しない。
使われ方：HTT 4.2.4.1、反対の塔の標準添字への厳密な再表示。 -/
lemma strictCoherentCone_isLimit_iff_whisker {F : I ⥤ C} (c : Cone F) (G : J ⥤ I)
    [IsIso ((SSet.uliftFunctor.{v, u}).map (nerveMap G))] :
    IsLimitCone (strictCoherentCone c) ↔ IsLimitCone (strictCoherentCone (c.whisker G)) := by
  rw [strictCoherentCone_whisker]
  exact (coherentConeRestrict_isLimit_iff (strictCoherentCone c) _).trans
    (coherentConeCast_isLimit_iff _ _).symm

end
end SerrePositivity.InfinityCategories.HomotopyLimits
