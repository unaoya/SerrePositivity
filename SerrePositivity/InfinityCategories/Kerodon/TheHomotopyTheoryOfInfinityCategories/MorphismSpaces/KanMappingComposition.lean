module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanMappingSpanComposition

/-! # 元の二辺と実三角形を保持する合成
概要：端点の合う元の二辺から、元の二辺を両面に持つ実合成三角形を構成する。
方針：辺の合成類を代表し、証明済みの合成構造の判定から全三辺の実二単体を得る。
規約：結論を成分の等式で終えず、合成辺と全三角形を保持する。
使われ方：実補正有限列を、全合成証人を記録した一本の比較辺へまとめる。

対応節は Kerodon 4.6（Tag 01J3）。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open _root_.SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial

/-- 元の二辺を二面として保持する、実合成辺と全三角形。 -/
structure KanMappingComposition {E : SSet.{u}} {x y z : E _⦋0⦌}
    (a : E.Edge x y) (b : E.Edge y z) where
  /-- 元の二辺の実合成辺。 -/
  edge : E.Edge x z
  /-- 元の二辺と合成辺の全二単体。 -/
  triangle : SSet.Edge.CompStruct a b edge

/-- 二辺の合成を、全三辺と実二単体を伴って構成する。 -/
def kanMappingComposition {E : SSet.{u}} [Quasicategory E] {x y z : E _⦋0⦌}
    (a : E.Edge x y) (b : E.Edge y z) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.KanMappingComposition a b := by
  let hex := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective x z
    (SSet.Truncated.HomotopyCategory.homMk a.toTruncated ≫
      SSet.Truncated.HomotopyCategory.homMk b.toTruncated)
  let e := SSet.Edge.ofTruncated hex.choose
  exact ⟨e, SSet.Edge.CompStruct.ofTruncated
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.compStruct_nonempty_of_homMk_fac hex.choose_spec.symm).some⟩

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.KanMappingComposition (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.KanMappingComposition := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.KanMappingComposition

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.kanMappingComposition (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.kanMappingComposition := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.kanMappingComposition

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.KanMappingComposition._sizeOf_1 (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.KanMappingComposition._sizeOf_1 := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.KanMappingComposition._sizeOf_1

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.KanMappingComposition._sizeOf_inst (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.KanMappingComposition._sizeOf_inst := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.KanMappingComposition._sizeOf_inst

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.KanMappingComposition.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.KanMappingComposition.casesOn := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.KanMappingComposition.casesOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.KanMappingComposition.ctorIdx (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.KanMappingComposition.ctorIdx := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.KanMappingComposition.ctorIdx

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.KanMappingComposition.edge (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.KanMappingComposition.edge := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.KanMappingComposition.edge

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.KanMappingComposition.mk (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.KanMappingComposition.mk := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.KanMappingComposition.mk

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.KanMappingComposition.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.KanMappingComposition.noConfusion := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.KanMappingComposition.noConfusion

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.KanMappingComposition.noConfusionType (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.KanMappingComposition.noConfusionType := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.KanMappingComposition.noConfusionType

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.KanMappingComposition.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.KanMappingComposition.rec := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.KanMappingComposition.rec

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.KanMappingComposition.recOn (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.KanMappingComposition.recOn := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.KanMappingComposition.recOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.KanMappingComposition.triangle (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.KanMappingComposition.triangle := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.KanMappingComposition.triangle

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.kanMappingComposition._proof_1 := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.kanMappingComposition._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.kanMappingComposition._proof_2 := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.kanMappingComposition._proof_2

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.KanMappingComposition.mk._flat_ctor (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.KanMappingComposition.mk._flat_ctor := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.KanMappingComposition.mk._flat_ctor

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.KanMappingComposition.mk.inj := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.KanMappingComposition.mk.inj

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.KanMappingComposition.mk.injEq := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.KanMappingComposition.mk.injEq

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.KanMappingComposition.mk.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.KanMappingComposition.mk.noConfusion := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.KanMappingComposition.mk.noConfusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.KanMappingComposition.mk.sizeOf_spec := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.KanMappingComposition.mk.sizeOf_spec
