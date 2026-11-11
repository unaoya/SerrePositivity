module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleLongHomFamilyLift

/-!
概要：宇宙を上げた関手空間内の全族から、元の小さい native Hom を入力点で読む。
方針：関手頂点の逆と宇宙持ち上げの完全忠実性を使う。
規約：始域の全 path の写像を回収し、合成端の評価も保持する。
使われ方：Ind-S (9) の L の元から有限制御二単体の指定値への変換。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 宇宙を上げた全関手族の一入力を、元の小さい射へ戻す。 -/
def nativeHomFamilyValue {A H : SSet.{u}} {K : SSet.{max u v}}
    (q : K ⟶ (ihom ((SSet.uliftFunctor.{v, u}).obj A)).obj
      ((SSet.uliftFunctor.{v, u}).obj H)) (k : K _⦋0⦌) : A ⟶ H :=
  (SSet.uliftFunctor.{v, u}).preimage
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm (q.app (Opposite.op ⦋0⦌) k))

/-- 小さい射を再び持ち上げると、元の全関手族の同じ一入力そのもの。 -/
lemma nativeHomFamilyValue_map {A H : SSet.{u}} {K : SSet.{max u v}}
    (q : K ⟶ (ihom ((SSet.uliftFunctor.{v, u}).obj A)).obj
      ((SSet.uliftFunctor.{v, u}).obj H)) (k : K _⦋0⦌) :
    (SSet.uliftFunctor.{v, u}).map (nativeHomFamilyValue q k) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm (q.app (Opposite.op ⦋0⦌) k) := by
  exact (SSet.uliftFunctor.{v, u}).map_preimage _

/-- 全 native Hom の関手頂点を厳密に回収する。 -/
lemma nativeHomFamilyValue_vertex {A H : SSet.{u}} {K : SSet.{max u v}}
    (q : K ⟶ (ihom ((SSet.uliftFunctor.{v, u}).obj A)).obj
      ((SSet.uliftFunctor.{v, u}).obj H)) (k : K _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{v, u}).map (nativeHomFamilyValue q k)) =
      q.app (Opposite.op ⦋0⦌) k := by
  rw [nativeHomFamilyValue_map]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).apply_symm_apply _

/-- 全族の評価式は、元の小さい射の同じ点での値を厳密に指定する。 -/
lemma nativeHomFamilyValue_evaluate {A H : SSet.{u}} {K : SSet.{max u v}}
    (q : K ⟶ (ihom ((SSet.uliftFunctor.{v, u}).obj A)).obj
      ((SSet.uliftFunctor.{v, u}).obj H)) (a : A _⦋0⦌)
    (c : K ⟶ (SSet.uliftFunctor.{v, u}).obj H)
    (hc : q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (X := (SSet.uliftFunctor.{v, u}).obj A)
      (Y := (SSet.uliftFunctor.{v, u}).obj H) (ULift.up a) = c) (k : K _⦋0⦌) :
    ULift.up ((nativeHomFamilyValue q k).app (Opposite.op ⦋0⦌) a) =
      c.app (Opposite.op ⦋0⦌) k := by
  have hh := congrArg (fun F => F.app (Opposite.op ⦋0⦌) k) hc
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up a)).app (Opposite.op ⦋0⦌)
    (q.app (Opposite.op ⦋0⦌) k) = _ at hh
  rw [← nativeHomFamilyValue_vertex q k, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex] at hh
  exact hh

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
