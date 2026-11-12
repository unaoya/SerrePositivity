module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.QuasicategoryCore
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.OuterHornConverse
public import Mathlib.Tactic.CrossRefAttribute

/-! # Kan 始域からの射の実 core 制限
概要：Kan 複体からの任意の単体的射を、元の標的の core へ持ち上げる。
方針：始域のホモトピー圏の亜群性から全辺の可逆性を得て、元の core 持ち上げを使う。
規約：元の全単体を変えない。使われ方：全 native Perf 関手族の豊穣射の core 化。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Opposite SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- Kan 始域の元の各辺は、そのホモトピー圏で可逆。 -/
lemma kanSource_edge_isInvertible {X : SSet.{u}} [KanComplex X] (s : X _⦋1⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex s) := by
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.isInvertibleEdge_of_hasFinalHornFillers (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex s)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.hasFinalHornFillers_of_kanComplex _)

/-- Kan 始域からの元の射を、そのまま標的の実 core に持ち上げる。 -/
@[kerodon 01D8]
def kanSourceCoreMap {X Y : SSet.{u}} [KanComplex X] (f : X ⟶ Y) :
    X ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore Y : SSet) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreLift f (fun s =>
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
      (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex s).map ((truncation 2).map f))
      (f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (f.app (op ⦋1⦌) s)) rfl).mp
      ((kanSource_edge_isInvertible s).map f))

/-- 実 core 持ち上げは、包含後に同じ元の射を厳密に回収する。 -/
@[kerodon 01D8]
lemma kanSourceCoreMap_inclusion {X Y : SSet.{u}} [KanComplex X] (f : X ⟶ Y) :
    kanSourceCoreMap f ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore Y).ι = f := rfl

end SerrePositivity.KST.SConstruction
