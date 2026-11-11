module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.InitialUniqueness
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：図式上の錐と極限を slice の頂点と終対象として定義する。
方針：錐は Δ[0]⋆K からの固定条件付きの射、極限性は slice の終対象の充填条件。
規約：一意性は h(slice) での同型であり、頂点の命題的等号を主張しない。
使われ方：HTT Definition 1.2.13.4、Kerodon §7.1（Tag 02H1） の極限、引き戻しと始対象の cofinality。
-/

@[expose] public section

universe u

open CategoryTheory SSet
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 概要：図式 p 上の錐は、K 上 p に一致する Δ[0]⋆K からの射。
方針：固定条件を部分型で保持し、slice の零単体と同じ型にする。
規約：錐の頂点は左因子。
使われ方：HTT Definition 1.2.13.4、Kerodon §7.1（Tag 02H1） の錐。 -/
@[kerodon 02JM]
abbrev JoinCone {K X : SSet.{u}} (p : K ⟶ X) :=
  {F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) K ⟶ X // _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] K ≫ F = p}

/-- 概要：join による錐の頂点。
方針：slice 射影の零次成分を使う。
規約：値は X の零単体。
使われ方：HTT §1.2.13、Kerodon §7.1（Tag 02H1） の極限対象。 -/
def JoinCone.vertex {K X : SSet.{u}} {p : K ⟶ X} (c : JoinCone p) : X _⦋0⦌ :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p).app (Opposite.op ⦋0⦌) c

/-- 概要：錐の頂点は錐を左因子へ制限した射の Yoneda 表示。
方針：slice 射影の定義を展開する。
規約：錐の固定条件には依存しない。
使われ方：HTT §1.2.13、Kerodon §7.1（Tag 02H1） の具体的な錐との比較。 -/
lemma JoinCone.vertex_eq {K X : SSet.{u}} {p : K ⟶ X} (c : JoinCone p) :
    c.vertex = SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[0] K ≫ c.val) := rfl

/-- 概要：錐が極限錐であることは、対応する slice の頂点が終対象であること。
方針：A2e の境界充填条件を slice の単体集合に適用する。
規約：定義自体に quasicategory の仮定は不要。
使われ方：HTT Definition 1.2.13.4、Kerodon §7.1（Tag 02H1） の極限。 -/
@[kerodon 02JM]
def IsLimitCone {K X : SSet.{u}} {p : K ⟶ X} (c : JoinCone p) : Prop :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p) c

/-- 概要：図式が極限を持つとは極限錐が存在すること。
方針：直接構成した join の錐とその極限性の存在量化を使う。
規約：極限錐の選択は構造に含めない。
使われ方：HTT §1.2.13、Kerodon §7.1（Tag 02H1） の極限の存在。 -/
def HasLimit {K X : SSet.{u}} (p : K ⟶ X) : Prop := ∃ c : JoinCone p, IsLimitCone c

/-- 概要：極限性は錐上の slice 射影が trivial Kan fibration であることと同値。
方針：終対象の trivial Kan fibration による特徴づけを slice に適用する。
規約：二重の slice は単体集合として直接構成したもの。
使われ方：HTT §1.2.12–1.2.13、Kerodon §7.1（Tag 02H1） の極限の充填条件。 -/
lemma isLimitCone_iff_trivialKanFibration {K X : SSet.{u}} {p : K ⟶ X} (c : JoinCone p) :
    IsLimitCone c ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (K := Δ[0]) (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p) (SSet.yonedaEquiv.symm c)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.isTerminalVertex_iff_trivialKanFibration (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p) c

/-- 概要：二つの極限錐は図式上の slice のホモトピー圏で同型。
方針：slice の quasicategory 性と終対象の一意性を使う。
規約：仮定は X の quasicategory 性と両錐の極限性。
使われ方：HTT §1.2.13、Kerodon §7.1（Tag 02H1） の極限の一意性。 -/
noncomputable def limitConeIso {K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X}
    (c d : JoinCone p) (hc : IsLimitCone c) (hd : IsLimitCone d) :
    (SSet.HomotopyCategory.mk c : hoFunctor.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p)) ≅ SSet.HomotopyCategory.mk d :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.terminalVertexIso hc hd

/-- 概要：二つの極限錐の頂点は X のホモトピー圏で同型。
方針：h(slice) での錐の同型を射影が誘導する関手で写す。
規約：同型は極限錐全体の同型から得る。
使われ方：HTT §1.2.13、Kerodon §7.1（Tag 02H1） の極限対象の一意性。 -/
noncomputable def limitVertexIso {K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X}
    (c d : JoinCone p) (hc : IsLimitCone c) (hd : IsLimitCone d) :
    (SSet.HomotopyCategory.mk c.vertex : hoFunctor.obj X) ≅ SSet.HomotopyCategory.mk d.vertex :=
  (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p)).toFunctor.mapIso (limitConeIso c d hc hd)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
