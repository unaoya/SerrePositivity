module
public import SerrePositivity.KST.Fibration.ZeroStableHom
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.InitialTransport

/-! # 元の完全関手の Kan Hom の辺に沿う、実零値条件の移送 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 元の Kan Hom の実辺に沿い、同じ関手圏の零対象条件を移送する。 -/
theorem stableHomZeroVertex_of_edge {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}}
    {v w : (A ⟶[SSet.{u}] B) _⦋0⦌} (e : SSet.Edge v w)
    (hv : StableHomZeroVertex A B v) : StableHomZeroVertex A B w := by
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e.toTruncated :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.isInvertibleEdge_of_hasFinalHornFillers _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.hasFinalHornFillers_of_kanComplex _)
  letI : IsIso (Truncated.HomotopyCategory.homMk e.toTruncated) := he
  exact hv.of_vertexIso ((hoFunctor.map (stableHomAmbient A B)).toFunctor.mapIso
    (asIso (Truncated.HomotopyCategory.homMk e.toTruncated)))

/-- 元の Kan Hom の辺の両端で、零値条件は同値である。 -/
theorem stableHomZeroVertex_iff_of_edge {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}}
    {v w : (A ⟶[SSet.{u}] B) _⦋0⦌} (e : SSet.Edge v w) :
    StableHomZeroVertex A B v ↔ StableHomZeroVertex A B w := by
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e.toTruncated :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.isInvertibleEdge_of_hasFinalHornFillers _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.hasFinalHornFillers_of_kanComplex _)
  letI : IsIso (Truncated.HomotopyCategory.homMk e.toTruncated) := he
  let E := (hoFunctor.map (stableHomAmbient A B)).toFunctor.mapIso
    (asIso (Truncated.HomotopyCategory.homMk e.toTruncated))
  exact ⟨fun hv => hv.of_vertexIso E, fun hw => hw.of_vertexIso E.symm⟩

end SerrePositivity.KST.Fibration
