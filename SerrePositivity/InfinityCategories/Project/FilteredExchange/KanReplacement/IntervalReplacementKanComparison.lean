module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePath
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePathReplacement
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.IntervalDiagram
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.KanEquivalencePaths

/-!
概要：Kan 標的では区間の path 置換は既存の可逆 path 置換に同型。
方針：可逆 path の包含が同型であることを引き戻しに移す。
規約：path 座標と元の始域の座標を保つ。
使われ方：filtered 連続性の具体的な模型を既存の Kan fibration に接続する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

variable {X Y : SSet.{u}} [KanComplex Y]

/-- 概要：可逆 path 置換から区間関手の path 置換への標準比較同型。
方針：Kan 標的では全ての path が可逆なので、包含を引き戻す。
規約：元の射 f は任意。使われ方：既存の置換の相対充填性の移送。 -/
def equivalenceIntervalReplacementIso (f : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacement f ≅ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacement f :=
  asIso (pullback.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint Y 0) f
    ((_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalEndpointNatTrans 0).app Y) f (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι Y) (𝟙 X) (𝟙 Y)
    (by rw [Category.comp_id]; rfl) (by rw [Category.comp_id, Category.id_comp]))

/-- 概要：置換の比較は path 座標で可逆 path の包含に一致する。
方針：引き戻しの比較の第一射影の式。
規約：全ての高次の path を保つ。使われ方：終点評価の同定。 -/
lemma equivalenceIntervalReplacementIso_fst (f : X ⟶ Y) :
    (equivalenceIntervalReplacementIso f).hom ≫
        pullback.fst ((_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalEndpointNatTrans 0).app Y) f =
      pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint Y 0) f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι Y := by
  rw [equivalenceIntervalReplacementIso, asIso_hom, pullback.map, pullback.lift_fst]

/-- 概要：置換の比較は元の始域の座標を保つ。
方針：引き戻しの比較の第二射影の式。
規約：射影は元の射そのもの。使われ方：元の入力の同定。 -/
lemma equivalenceIntervalReplacementIso_snd (f : X ⟶ Y) :
    (equivalenceIntervalReplacementIso f).hom ≫
        pullback.snd ((_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalEndpointNatTrans 0).app Y) f =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection f := by
  rw [equivalenceIntervalReplacementIso, asIso_hom, pullback.map, pullback.lift_snd,
    Category.comp_id]
  rfl

/-- 概要：置換の比較は終点の射を厳密に保つ。
方針：path 座標の式と可逆 path の終点の定義を使う。
規約：ホモトピーによる比較ではなく射の等式。使われ方：Kan fibration 性の移送。 -/
lemma equivalenceIntervalReplacementIso_endpoint (f : X ⟶ Y) :
    (equivalenceIntervalReplacementIso f).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacementEndpoint f =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap f := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacementEndpoint, ← Category.assoc, equivalenceIntervalReplacementIso_fst,
    Category.assoc]
  rfl

end SerrePositivity.InfinityCategories.Project.FilteredExchange
