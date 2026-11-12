module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.EquivalenceAllLimits
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：関手 ∞ 圏の図式と錐の各点での評価。
方針：内部 Hom の評価を既存の join の錐と極限性に接続する。
規約：点ごとの極限性と関手 ∞ 圏での極限性の比較は別に証明する。
使われ方：HTT Proposition 5.1.2.2、Kerodon §7.1.8（Tag 02X8）（旧参照 §7.1.6）。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 概要：関手 ∞ 圏の図式をパラメーターの一頂点で評価する。
方針：評価の射で後合成する。
規約：図式の添字 J とパラメーター K は任意の単体集合。
使われ方：HTT 5.1.2.2、Kerodon Definition 7.1.8.1（Tag 05QF） の点ごとの図式。 -/
def evaluateFunctorDiagram {J K X : SSet.{u}} (p : J ⟶ (ihom K).obj X)
    (k : K _⦋0⦌) : J ⟶ X := p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k

/-- 概要：関手 ∞ 圏の錐をパラメーターの一頂点で評価する。
方針：錐の後合成で固定図式も同時に評価する。
規約：評価後も同じ添字の図式上の join の錐。
使われ方：HTT 5.1.2.2、Kerodon Definition 7.1.8.1（Tag 05QF） の点ごとの錐。 -/
@[kerodon 05QF]
def evaluateFunctorCone {J K X : SSet.{u}} {p : J ⟶ (ihom K).obj X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (k : K _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (evaluateFunctorDiagram p k) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k) c

/-- 概要：評価した錐の頂点は元の錐の頂点を評価したもの。
方針：錐の後合成の頂点の計算を使う。
規約：内部 Hom の頂点をそのまま評価する。
使われ方：HTT 5.1.2.2 の極限対象の成分表示。 -/
lemma evaluateFunctorCone_vertex {J K X : SSet.{u}} {p : J ⟶ (ihom K).obj X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (k : K _⦋0⦌) :
    (evaluateFunctorCone c k).vertex = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k).app (Opposite.op ⦋0⦌) c.vertex :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone_vertex _ c

/-- 概要：関手 ∞ 圏の図式の全ての評価図式が極限を持つという条件。
方針：各頂点における既存の HasLimit を要求する。
規約：選んだ錐どうしの自然性はこの条件に含まない。
使われ方：Kerodon Proposition 7.1.8.3（Tag 02X9） の双対、HTT 5.1.2.2 の存在仮定。 -/
def HasPointwiseLimits {J K X : SSet.{u}} (p : J ⟶ (ihom K).obj X) : Prop :=
  ∀ k : K _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit (evaluateFunctorDiagram p k)

/-- 概要：関手 ∞ 圏の錐が各点で極限錐であるという条件。
方針：同じ自然な錐の全ての評価に IsLimitCone を要求する。
規約：独立に選んだ錐の族ではなく、既に関手 ∞ 圏で定義された錐を扱う。
使われ方：Kerodon Definition 7.1.8.1（Tag 05QF）、HTT 5.1.2.2 の極限判定。 -/
@[kerodon 05QF]
def IsPointwiseLimitCone {J K X : SSet.{u}} {p : J ⟶ (ihom K).obj X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) : Prop := ∀ k : K _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (evaluateFunctorCone c k)

/-- 概要：点ごとの極限錐があれば全ての評価図式は極限を持つ。
方針：与えられた錐の各評価を取る。
規約：この補題には quasicategory 性を必要としない。
使われ方：HTT 5.1.2.2 の存在条件と錐の条件の接続。 -/
lemma IsPointwiseLimitCone.hasPointwiseLimits {J K X : SSet.{u}}
    {p : J ⟶ (ihom K).obj X} {c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p} (hc : IsPointwiseLimitCone c) :
    HasPointwiseLimits p := fun k ↦ ⟨evaluateFunctorCone c k, hc k⟩

/-- 概要：同じ図式上の同型な錐の間で点ごとの極限性は保たれる。
方針：slice の同型を各評価の後合成で写し、極限錐の同型不変性を使う。
規約：同型は関手 ∞ 圏の錐の slice のホモトピー圏で取る。
使われ方：Kerodon Proposition 7.1.8.3（Tag 02X9） の一意性による逆方向。 -/
lemma IsPointwiseLimitCone.of_vertexIso {J K X : SSet.{u}} [Quasicategory X]
    {p : J ⟶ (ihom K).obj X} {c d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p}
    (hc : IsPointwiseLimitCone c) (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p) c d) :
    IsPointwiseLimitCone d := by
  intro k
  exact (hc k).of_vertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k)))

/-- 概要：同じ図式上の同型な錐の点ごとの極限性は同値。
方針：同型と逆同型を使う。
規約：標的 X は quasicategory、パラメーターと図式の形は任意。
使われ方：Kerodon Proposition 7.1.8.3（Tag 02X9） の双対。 -/
lemma isPointwiseLimitCone_iff_of_vertexIso {J K X : SSet.{u}} [Quasicategory X]
    {p : J ⟶ (ihom K).obj X} {c d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p) c d) : IsPointwiseLimitCone c ↔ IsPointwiseLimitCone d :=
  ⟨fun hc ↦ hc.of_vertexIso e, fun hd ↦ hd.of_vertexIso e.symm⟩

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
