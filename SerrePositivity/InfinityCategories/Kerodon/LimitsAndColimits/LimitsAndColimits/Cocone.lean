module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoreLimit
public import Mathlib.Tactic.CrossRefAttribute

/-! # join と coslice による余極限錐

概要：図式 p の余錐を K⋆Δ[0] からの射とし、その coslice の始対象を余極限と定義する。
方針：A2 の sliceUnder と sliceUnderEquiv を使い、極限の左右双対を直接構成する。
規約：頂点は右因子、図式は左因子で固定する。使われ方：HA §1.1 の cofiber・懸垂。

対応節は Kerodon 7.1（Tag 02H1）。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open CategoryTheory SSet
open scoped _root_.Simplicial

/-- 概要：図式 p の余錐は p に制限される K⋆Δ[0] からの射。
方針：固定条件を部分型で保持する。
規約：sliceUnder p の零単体と同じ型。使われ方：余極限の定義の入力。 -/
@[kerodon 02JN]
abbrev JoinCocone {K X : SSet.{u}} (p : K ⟶ X) :=
  {F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K (Δ[0] : SSet.{u}) ⟶ X // _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K Δ[0] ≫ F = p}

/-- 概要：join 余錐の頂点。
方針：coslice 射影の零次成分で右因子の値を取る。
規約：X の実際の零単体。使われ方：余極限対象の比較。 -/
def JoinCocone.vertex {K X : SSet.{u}} {p : K ⟶ X} (c : JoinCocone p) : X _⦋0⦌ :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p).app (Opposite.op ⦋0⦌) c

/-- 概要：余錐の頂点は右因子への制限の Yoneda 座標である。
方針：coslice 射影を展開する。
規約：固定条件の証明には依存しない。使われ方：余錐の具体的な頂点の計算。 -/
lemma JoinCocone.vertex_eq {K X : SSet.{u}} {p : K ⟶ X} (c : JoinCocone p) :
    c.vertex = SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K Δ[0] ≫ c.val) := rfl

/-- 概要：余極限余錐は coslice の始対象である。
方針：A2e の始対象の境界充填条件を適用する。
規約：定義には quasicategory 性を要求しない。使われ方：押し出し・cofiber・懸垂。 -/
@[kerodon 02JN]
def IsColimitCone {K X : SSet.{u}} {p : K ⟶ X} (c : JoinCocone p) : Prop :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p) c

/-- 概要：余極限の存在は余極限余錐の存在である。
方針：余錐とその充填条件を存在量化する。
規約：選択は定義に含めない。使われ方：有限余極限と安定性の定義。 -/
def HasColimit {K X : SSet.{u}} (p : K ⟶ X) : Prop :=
  ∃ c : JoinCocone p, IsColimitCone c

/-- 概要：余極限性は余錐の頂点下の射影の trivial Kan fibration 性と同値。
方針：A2e の coslice 射影による始対象の判定を使う。
規約：二重の coslice を直接用いる。使われ方：余極限の持ち上げ問題。 -/
lemma isColimitCone_iff_trivialKanFibration {K X : SSet.{u}} {p : K ⟶ X}
    (c : JoinCocone p) : IsColimitCone c ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection
        (K := Δ[0]) (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p) (SSet.yonedaEquiv.symm c)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.isInitialVertex_iff_trivialKanFibration (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p) c

/-- 概要：二つの余極限余錐は図式下の coslice のホモトピー圏で同型である。
方針：始対象の一意性を A2f の双対として適用する。
規約：X の quasicategory 性を仮定する。使われ方：余極限の選択の比較。 -/
def colimitConeIso {K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X}
    (c d : JoinCocone p) (hc : IsColimitCone c) (hd : IsColimitCone d) :
    (SSet.HomotopyCategory.mk c : hoFunctor.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p)) ≅ SSet.HomotopyCategory.mk d :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.initialVertexIso hc hd

/-- 概要：二つの余極限対象は X のホモトピー圏で同型である。
方針：coslice 内の同型を射影で送る。
規約：同型は余錐全体の比較から得る。使われ方：cofiber・Σ の選択の比較。 -/
def colimitVertexIso {K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X}
    (c d : JoinCocone p) (hc : IsColimitCone c) (hd : IsColimitCone d) :
    (SSet.HomotopyCategory.mk c.vertex : hoFunctor.obj X) ≅ SSet.HomotopyCategory.mk d.vertex :=
  (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p)).toFunctor.mapIso (colimitConeIso c d hc hd)

/-- 概要：パラメータ付き余錐は coslice への射と同じである。
方針：A2 の一般の sliceUnderEquiv を使う。
規約：任意のパラメータ単体集合 A。使われ方：余錐の射とホモトピーの構成。 -/
def joinCoconeFamilyEquiv {A K X : SSet.{u}} (p : K ⟶ X) :
    (A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p) ≃ {F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K A ⟶ X // _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K A ≫ F = p} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderEquiv p

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
