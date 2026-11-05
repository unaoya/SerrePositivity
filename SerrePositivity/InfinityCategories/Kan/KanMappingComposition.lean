module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Kan.KanMappingSpanComposition

/-! # 元の二辺と実三角形を保持する合成
概要：端点の合う元の二辺から、元の二辺を両面に持つ実合成三角形を構成する。
方針：辺の合成類を代表し、証明済みの合成構造の判定から全三辺の実二単体を得る。
規約：結論を成分の等式で終えず、合成辺と全三角形を保持する。
使われ方：実補正有限列を、全合成証人を記録した一本の比較辺へまとめる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Kan
open SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped _root_.Simplicial

/-- 元の二辺を二面として保持する、実合成辺と全三角形。 -/
structure KanMappingComposition {E : SSet.{u}} {x y z : E _⦋0⦌}
    (a : E.Edge x y) (b : E.Edge y z) where
  /-- 元の二辺の実合成辺。 -/
  edge : E.Edge x z
  /-- 元の二辺と合成辺の全二単体。 -/
  triangle : SSet.Edge.CompStruct a b _root_.SerrePositivity.InfinityCategories.Kan.KanMappingComposition.edge

/-- 二辺の合成を、全三辺と実二単体を伴って構成する。 -/
def kanMappingComposition {E : SSet.{u}} [Quasicategory E] {x y z : E _⦋0⦌}
    (a : E.Edge x y) (b : E.Edge y z) : _root_.SerrePositivity.InfinityCategories.Kan.KanMappingComposition a b := by
  let hex := homotopyCategory_homMk_surjective x z
    (SSet.Truncated.HomotopyCategory.homMk a.toTruncated ≫
      SSet.Truncated.HomotopyCategory.homMk b.toTruncated)
  let e := SSet.Edge.ofTruncated hex.choose
  exact ⟨e, SSet.Edge.CompStruct.ofTruncated
    (compStruct_nonempty_of_homMk_fac hex.choose_spec.symm).some⟩

end SerrePositivity.InfinityCategories.Kan

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.KanMappingComposition (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.KanMappingComposition := _root_.SerrePositivity.InfinityCategories.Kan.KanMappingComposition

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.kanMappingComposition (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.kanMappingComposition := _root_.SerrePositivity.InfinityCategories.Kan.kanMappingComposition

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.KanMappingComposition._sizeOf_1 (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.KanMappingComposition._sizeOf_1 := _root_.SerrePositivity.InfinityCategories.Kan.KanMappingComposition._sizeOf_1

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.KanMappingComposition._sizeOf_inst (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.KanMappingComposition._sizeOf_inst := _root_.SerrePositivity.InfinityCategories.Kan.KanMappingComposition._sizeOf_inst

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.KanMappingComposition.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.KanMappingComposition.casesOn := _root_.SerrePositivity.InfinityCategories.Kan.KanMappingComposition.casesOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.KanMappingComposition.ctorIdx (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.KanMappingComposition.ctorIdx := _root_.SerrePositivity.InfinityCategories.Kan.KanMappingComposition.ctorIdx

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.KanMappingComposition.edge (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.KanMappingComposition.edge := _root_.SerrePositivity.InfinityCategories.Kan.KanMappingComposition.edge

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.KanMappingComposition.mk (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.KanMappingComposition.mk := _root_.SerrePositivity.InfinityCategories.Kan.KanMappingComposition.mk

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.KanMappingComposition.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.KanMappingComposition.noConfusion := _root_.SerrePositivity.InfinityCategories.Kan.KanMappingComposition.noConfusion

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.KanMappingComposition.noConfusionType (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.KanMappingComposition.noConfusionType := _root_.SerrePositivity.InfinityCategories.Kan.KanMappingComposition.noConfusionType

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.KanMappingComposition.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.KanMappingComposition.rec := _root_.SerrePositivity.InfinityCategories.Kan.KanMappingComposition.rec

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.KanMappingComposition.recOn (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.KanMappingComposition.recOn := _root_.SerrePositivity.InfinityCategories.Kan.KanMappingComposition.recOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.KanMappingComposition.triangle (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.KanMappingComposition.triangle := _root_.SerrePositivity.InfinityCategories.Kan.KanMappingComposition.triangle

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.kanMappingComposition._proof_1 := _root_.SerrePositivity.InfinityCategories.Kan.kanMappingComposition._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.kanMappingComposition._proof_2 := _root_.SerrePositivity.InfinityCategories.Kan.kanMappingComposition._proof_2

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.KanMappingComposition.mk._flat_ctor (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.KanMappingComposition.mk._flat_ctor := _root_.SerrePositivity.InfinityCategories.Kan.KanMappingComposition.mk._flat_ctor

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.KanMappingComposition.mk.inj := _root_.SerrePositivity.InfinityCategories.Kan.KanMappingComposition.mk.inj

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.KanMappingComposition.mk.injEq := _root_.SerrePositivity.InfinityCategories.Kan.KanMappingComposition.mk.injEq

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.KanMappingComposition.mk.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.KanMappingComposition.mk.noConfusion := _root_.SerrePositivity.InfinityCategories.Kan.KanMappingComposition.mk.noConfusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.KanMappingComposition.mk.sizeOf_spec := _root_.SerrePositivity.InfinityCategories.Kan.KanMappingComposition.mk.sizeOf_spec
