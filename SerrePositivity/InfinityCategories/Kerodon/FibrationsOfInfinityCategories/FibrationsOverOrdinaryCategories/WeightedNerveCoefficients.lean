module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.PrefixOverWeight

/-!
概要：Bousfield–Kan 重みの自然変換から weighted nerve の係数を作る。
方針：射列の初区間の標準単体とパラメータの制限を直積にまとめて評価する。
規約：全ての単体作用素と整合させ、係数の Kan 性は要求しない。
使われ方：Kerodon 5.3.3.1（Tag 025X）、7.5.3.12（Tag 03B1） の重み付き end から切断空間への比較。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
variable {I : Type u} [SmallCategory I] {A : SSet.{u}}

/-- 概要：初区間の over 圏の単体とパラメータを同時に評価する標準の自然変換。
方針：初区間の重みの射と、パラメータの標準単体への制限を直積へ持ち上げる。
規約：パラメータの単体は Δ[n] からの射で表示する。
使われ方：Kerodon 5.3.3.1（Tag 025X）、7.5.3.12（Tag 03B1） の weighted nerve の係数の構成。 -/
def prefixOverParameter {n : ℕ} (σ : ComposableArrows I n) (a : (Δ[n] : SSet.{u}) ⟶ A) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight n ⟶ σ ⋙ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I ⊗ (Functor.const I).obj A) where
  app i := lift ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.prefixOverWeight σ).app i)
    (stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion i.val n (Nat.le_of_lt_succ i.isLt)) ≫ a)
  naturality i j f := by
    change stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion i.val j.val (leOfHom f)) ≫
      lift _ _ = lift _ _ ≫ ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I).map (σ.map f) ⊗ₘ 𝟙 A)
    rw [comp_lift, lift_map, Category.comp_id]
    apply congrArg₂ lift
    · exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.prefixOverChain_yoneda_inclusion σ (leOfHom f)
    · rw [← Category.assoc, ← Functor.map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion_comp]

/-- 概要：初区間とパラメータの自然変換は任意の単体作用素に沿う制限と可換。
方針：直積の二つの成分で over 圏の標準単体と初区間の包含の制限を比較する。
規約：パラメータは標準単体の射で前合成する。
使われ方：Kerodon 5.3.3.1（Tag 025X）、7.5.3.12（Tag 03B1） の weighted nerve への射の自然性。 -/
lemma prefixOverParameter_restriction {m n : SimplexCategory} (α : m ⟶ n)
    (σ : ComposableArrows I n.len) (a : (Δ[n.len] : SSet.{u}) ⟶ A) :
    prefixOverParameter ((SimplexCategory.toCat.map α).toFunctor ⋙ σ)
        (stdSimplex.map α ≫ a) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeightRestriction α ≫ Functor.whiskerLeft
        (SimplexCategory.toCat.map α).toFunctor (prefixOverParameter σ a) := by
  apply NatTrans.ext
  funext i
  change lift ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.prefixOverWeight ((SimplexCategory.toCat.map α).toFunctor ⋙ σ)).app i)
      (stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion i.val m.len _) ≫ (stdSimplex.map α ≫ a)) =
    stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixRestriction α i) ≫
      lift ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.prefixOverWeight σ).app (α.toOrderHom i))
        (stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion (α.toOrderHom i).val n.len
          (Nat.le_of_lt_succ (α.toOrderHom i).isLt)) ≫ a)
  rw [comp_lift]
  apply congrArg₂ lift
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.prefixOverChain_yoneda_restriction α σ i
  · rw [← Category.assoc, ← Functor.map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixRestriction_factor]
    simp only [Functor.map_comp, Category.assoc]

/-- 概要：Bousfield–Kan 重みとパラメータの自然変換を weighted nerve の係数へ変換する。
方針：初区間の標準の評価に自然変換を後合成する。
規約：底の射列 σ は固定し、係数だけを作る。
使われ方：Kerodon 5.3.3.1（Tag 025X）、7.5.3.12（Tag 03B1） の重み付き end の族から切断の族への構成。 -/
def weightedNerveCoefficients {H : I ⥤ SSet.{u}}
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I ⊗ (Functor.const I).obj A ⟶ H)
    {n : ℕ} (σ : ComposableArrows I n) (a : (Δ[n] : SSet.{u}) ⟶ A) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight n ⟶ σ ⋙ H :=
  prefixOverParameter σ a ≫ Functor.whiskerLeft σ η

/-- 概要：重み付き自然変換から作った係数は底の単体作用素に沿う制限と可換。
方針：標準の評価の制限公式と自然変換の合成の結合則を使う。
規約：全ての面と退化を同時に扱う。
使われ方：Kerodon 5.3.3.1（Tag 025X）、7.5.3.12（Tag 03B1） の切断を作る単体集合の射の自然性。 -/
lemma weightedNerveCoefficients_restriction {H : I ⥤ SSet.{u}}
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I ⊗ (Functor.const I).obj A ⟶ H)
    {m n : SimplexCategory} (α : m ⟶ n) (σ : ComposableArrows I n.len)
    (a : (Δ[n.len] : SSet.{u}) ⟶ A) :
    weightedNerveCoefficients η ((SimplexCategory.toCat.map α).toFunctor ⋙ σ)
        (stdSimplex.map α ≫ a) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeightRestriction α ≫ Functor.whiskerLeft
        (SimplexCategory.toCat.map α).toFunctor (weightedNerveCoefficients η σ a) := by
  apply NatTrans.ext
  funext i
  change (prefixOverParameter ((SimplexCategory.toCat.map α).toFunctor ⋙ σ)
    (stdSimplex.map α ≫ a)).app i ≫ η.app (σ.obj (α.toOrderHom i)) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeightRestriction α).app i ≫
      ((prefixOverParameter σ a).app (α.toOrderHom i) ≫ η.app (σ.obj (α.toOrderHom i)))
  rw [prefixOverParameter_restriction]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
