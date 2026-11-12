module
public import SerrePositivity.KST.SConstruction.Cofinality.CokernelNerveCoordinates
public import SerrePositivity.KST.SConstruction.Cofinality.GroupNerveHigherInput
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.HomotopyIso

/-!
概要：元の指定射の S 余核図式は同じ余核群の bar と単体的に同型となる。
方針：全区間値による比較射の次数ごとの全単射性を同型に束ねる。
規約：一般の群 nerve の消滅は採用済み Sp-8 (2) の明示入力に残す。
使われ方：相対 fiber の離散的障害の高次消滅。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：元の全 S 余核図式と同じ一段余核群の nerve との単体的同型。
方針：元の区間値による比較を各次数の辺座標の全単射性で同型にする。
規約：順射は元の全端点制限の値を保持する。
使われ方：障害図式の厳密な bar 同定。 -/
def cutCokernelBarIso {X Y : StableModel.{u}} (f : X ⟶ Y) :
    cutCokernelSimplicialSet f ≅
      nerve (AsSmall.{u} (SingleObj (Multiplicative (cutKZeroCokernel 1 f)))) :=
  NatIso.ofComponents
    (fun n => (Equiv.ofBijective (cutCokernelNerveSimplex f n.unop.len)
      (cutCokernelNerveSimplex_bijective f n.unop.len)).toIso)
    (fun {_ _} α => (cutCokernelNerveMap f).naturality α)

/-- 概要：元の S 余核図式の Kan 置換の二次以上のホモトピーは一意。
方針：実際の bar 同型で Sp-8 (2) の群 nerve の高次消滅を移す。
規約：一般供給だけを明示入力とし、共終性を仮定しない。
使われ方：相対 fiber の障害項から正次数 K 群の同型性を導く入口。 -/
lemma cutCokernel_higher_of_input (h : GroupNerveHigherVanishingInput.{u})
    {X Y : StableModel.{u}} (f : X ⟶ Y) (n : ℕ) (hn : 1 < n)
    (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj (cutCokernelSimplicialSet f)) _⦋0⦌) :
    Subsingleton (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj (cutCokernelSimplicialSet f)) n x) := by
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.mapIso (cutCokernelBarIso f)
  let : Subsingleton (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj
        (nerve (AsSmall.{u} (SingleObj (Multiplicative (cutKZeroCokernel 1 f)))))) n
          (e.hom.app (Opposite.op ⦋0⦌) x)) := cutCokernelBar_higher_of_input h 1 f n hn _
  exact Function.Injective.subsingleton ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanPiIsomorphism.of_iso e x n).1)

end SerrePositivity.KST.SConstruction.Cofinality
