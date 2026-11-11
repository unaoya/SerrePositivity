module
public import SerrePositivity.KST.SConstruction.ClosedSubcategoryStability
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.ExactFunctor

/-! # 閉じた安定部分圏の逆像と交わり
概要：完全関手による逆像と二つの条件の交わりは安定な閉性を保つ。
方針：零対象・全押し出し・全引き戻しの保存を各角で適用する。
規約：対象条件を同型で輸送する replete 性も保つ。使われ方：相対 cofiber 図式の閉性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 本レーンの零対象・cofiber 保存条件は既存の完全関手の条件を与える。 -/
lemma PreservesCofiberData.isExactFunctor {C D : SSet.{u}} {f : C ⟶ D}
    (hf : PreservesCofiberData f) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor f :=
  ⟨hf.1, hf.2⟩

/-- 完全関手による閉じた頂点条件の逆像。 -/
def ClosedStablePredicate.comap {X Y : StableModel.{u}} (P : ClosedStablePredicate Y)
    (f : X ⟶ Y) : ClosedStablePredicate X where
  predicate x := P.predicate (f.val.app (Opposite.op ⦋0⦌) x)
  of_iso hx e := P.of_iso hx (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e f.val)
  zero_mem hz := P.zero_mem (f.property.1 _ hz)
  pushout_mem F hF h00 h10 h01 := by
    have : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor f.val := f.property.isExactFunctor
    exact P.pushout_mem (F ≫ f.val) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesPushoutSquare f.val F hF) h00 h10 h01
  pullback_mem F hF h10 h01 h11 := by
    have : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor f.val := f.property.isExactFunctor
    exact P.pullback_mem (F ≫ f.val) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesPullbackSquare f.val F hF) h10 h01 h11

/-- 二つの安定な閉性条件の交わり。 -/
def ClosedStablePredicate.inter {X : StableModel.{u}} (P Q : ClosedStablePredicate X) :
    ClosedStablePredicate X where
  predicate x := P.predicate x ∧ Q.predicate x
  of_iso hx e := ⟨P.of_iso hx.1 e, Q.of_iso hx.2 e⟩
  zero_mem hz := ⟨P.zero_mem hz, Q.zero_mem hz⟩
  pushout_mem F hF h00 h10 h01 :=
    ⟨P.pushout_mem F hF h00.1 h10.1 h01.1, Q.pushout_mem F hF h00.2 h10.2 h01.2⟩
  pullback_mem F hF h10 h01 h11 :=
    ⟨P.pullback_mem F hF h10.1 h01.1 h11.1, Q.pullback_mem F hF h10.2 h01.2 h11.2⟩

/-- 全頂点を含む条件は全ての安定な閉性を満たす。 -/
def ClosedStablePredicate.top (X : StableModel.{u}) : ClosedStablePredicate X where
  predicate _ := True
  of_iso _ _ := trivial
  zero_mem _ := trivial
  pushout_mem _ _ _ _ _ := trivial
  pullback_mem _ _ _ _ _ := trivial

end SerrePositivity.KST.SConstruction
