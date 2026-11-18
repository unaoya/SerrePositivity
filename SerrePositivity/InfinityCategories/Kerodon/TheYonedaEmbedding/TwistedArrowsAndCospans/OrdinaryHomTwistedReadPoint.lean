module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.OrdinaryHomTwistedRead

/-!
概要：Hom の単一の元から作った指定 twisted arrow の読み戻しは元の射に戻る。
方針：零次の標準単体の両端と中央の射を評価する。
規約：全次数の逆関係とは分けて、同じ指定された単位の計算だけを扱う。
使われ方：Kerodon Proposition 8.1.1.10（Tag 03JN）、HTT 5.1.5.6 の模型比較の単位則。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
variable {C : Type u} [SmallCategory C]

/-- 同じ指定した Hom の元は零次の twisted arrow の往復で変わらない。
Kerodon Proposition 8.1.1.10（Tag 03JN）、模型比較の零次の単位則。 -/
lemma ordinaryHomTwistedRead_point (x : OrdinaryHomElements C) :
    (ordinaryHomTwistedRead (ordinaryHomTwistedSimplex (ComposableArrows.mk₀ x))).obj 0 = x := by
  refine Functor.Elements.ext
    ((ordinaryHomTwistedRead (ordinaryHomTwistedSimplex (ComposableArrows.mk₀ x))).obj 0)
    x (by rfl) ?_
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id, types_id_apply]
  change (𝟙 _ ≫ x.val ≫ 𝟙 _) = x.val
  simp only [Category.id_comp, Category.comp_id]

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
