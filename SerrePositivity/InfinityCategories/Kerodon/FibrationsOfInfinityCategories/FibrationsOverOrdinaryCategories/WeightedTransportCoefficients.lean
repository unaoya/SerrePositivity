module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.TransportSectionsComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NerveBaseChange

/-!
概要：係数の値を under 圏の全対象へ輸送し、weighted nerve の係数の族を作る。
方針：各構造射で係数を後合成し、初区間の包含でパラメータを制限する。
規約：係数図式の Kan 性はこの構成には不要。
使われ方：Kerodon 5.3.3.1（Tag 025X）、5.3.5.7（Tag 037Q）、7.5.4.6（Tag 03BB） の元の図式から strict transport への比較。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
variable {I : Type u} [SmallCategory I]

/-- 概要：H(i) のパラメータを under 圏の射列の各対象へ運んだ weighted nerve の係数。
方針：初区間でパラメータを制限し、i から各対象への構造射を H で写す。
規約：底の射列には Under.forget i を後合成する。
使われ方：Kerodon 5.3.3.1（Tag 025X）、5.3.5.7（Tag 037Q） の strict transport の標準の族。 -/
def weightedTransportCoefficients (H : I ⥤ SSet.{u}) {i : I} {n : ℕ}
    (σ : ComposableArrows (Under i) n) (a : (Δ[n] : SSet.{u}) ⟶ H.obj i) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight n ⟶ (σ ⋙ Under.forget i) ⋙ H where
  app k := stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion k.val n (Nat.le_of_lt_succ k.isLt)) ≫
    a ≫ H.map (σ.obj k).hom
  naturality k l f := by
    change stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion k.val l.val (leOfHom f)) ≫
      (stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion l.val n _) ≫ a ≫ H.map (σ.obj l).hom) =
        (stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion k.val n _) ≫ a ≫ H.map (σ.obj k).hom) ≫
          H.map (σ.map f).right
    rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion_comp]
    simp only [Category.assoc]
    rw [← H.map_comp, Under.w (σ.map f)]

/-- 概要：under 圏の輸送の係数は任意の面・退化の制限と可換。
方針：初区間の制限の分解公式と結合則を使う。
規約：パラメータは標準単体の射で前合成する。
使われ方：Kerodon 5.3.3.1（Tag 025X）、5.3.5.7（Tag 037Q） の weighted nerve への単体的射の自然性。 -/
lemma weightedTransportCoefficients_restriction (H : I ⥤ SSet.{u})
    {i : I} {m n : SimplexCategory} (α : m ⟶ n) (σ : ComposableArrows (Under i) n.len)
    (a : (Δ[n.len] : SSet.{u}) ⟶ H.obj i) :
    weightedTransportCoefficients H ((SimplexCategory.toCat.map α).toFunctor ⋙ σ)
        (stdSimplex.map α ≫ a) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeightRestriction α ≫ Functor.whiskerLeft
        (SimplexCategory.toCat.map α).toFunctor (weightedTransportCoefficients H σ a) := by
  apply NatTrans.ext
  funext k
  change stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion k.val m.len _) ≫
      (stdSimplex.map α ≫ a) ≫ H.map (σ.obj (α.toOrderHom k)).hom =
    stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixRestriction α k) ≫
      (stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion (α.toOrderHom k).val n.len _) ≫
        a ≫ H.map (σ.obj (α.toOrderHom k)).hom)
  simp only [← Category.assoc]
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixRestriction_factor]

/-- 概要：under 圏の始点を変える操作は係数の元の図式の射での輸送と一致する。
方針：Under.map の前合成の定義と H の合成の保存を使う。
規約：始点の射 f は任意。
使われ方：Kerodon 5.3.5.7（Tag 037Q）、7.5.4.6（Tag 03BB） の元の係数図式との自然な比較。 -/
lemma weightedTransportCoefficients_underMap (H : I ⥤ SSet.{u}) {i j : I} (f : i ⟶ j)
    {n : ℕ} (σ : ComposableArrows (Under j) n) (a : (Δ[n] : SSet.{u}) ⟶ H.obj i) :
    weightedTransportCoefficients H (σ ⋙ Under.map f) a =
      weightedTransportCoefficients H σ (a ≫ H.map f) := by
  apply NatTrans.ext
  funext k
  change stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion k.val n _) ≫ a ≫
    H.map (f ≫ (σ.obj k).hom) =
      stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion k.val n _) ≫ (a ≫ H.map f) ≫ H.map (σ.obj k).hom
  rw [H.map_comp]
  simp only [Category.assoc]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
