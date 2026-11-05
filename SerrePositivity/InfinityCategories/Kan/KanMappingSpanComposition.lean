module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Core.InvertibleEdgeLifting
public import SerrePositivity.InfinityCategories.Core.KanCharacterization

/-! # 元の二辺を保持する Kan 写像空間の span の合成
概要：共通の始点を持つ二辺を、指定した逆の三角形と合成三角形を保持して一本の辺にする。
方針：第一辺の逆を両逆三角形付きで取り、第二辺と指定した三辺で合成する。
規約：元の二辺を変更せず、選択した証人を全て実三角形として保存する。
使われ方：自然性 square から復号した二辺を、元の適合ホモトピーへ接続する。
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

/-- 元の span の第一辺の両逆証人と、元の第二辺との実合成三角形。 -/
structure KanMappingSpanComposition {E : SSet.{u}} {z x y : E _⦋0⦌}
    (a : E.Edge z x) (b : E.Edge z y) where
  /-- 第一辺の選んだ逆辺。 -/
  inverse : E.Edge x z
  /-- 第一辺と逆辺を合成する元の左逆三角形。 -/
  inverseLeft : SSet.Edge.CompStruct a inverse (SSet.Edge.id z)
  /-- 逆辺と第一辺を合成する元の右逆三角形。 -/
  inverseRight : SSet.Edge.CompStruct inverse a (SSet.Edge.id x)
  /-- span から得た実際の合成辺。 -/
  edge : E.Edge x y
  /-- 元の逆辺・元の第二辺・合成辺を保持する実三角形。 -/
  triangle : SSet.Edge.CompStruct inverse b edge

/-- 元の二辺を保持し、全ての証人を実三角形として伴う span の合成。 -/
def kanMappingSpanComposition {E : SSet.{u}} [KanComplex E] {z x y : E _⦋0⦌}
    (a : E.Edge z x) (b : E.Edge z y) : _root_.SerrePositivity.InfinityCategories.Kan.KanMappingSpanComposition a b := by
  have ha : IsInvertibleEdge a.toTruncated :=
    isInvertibleEdge_of_hasFinalHornFillers _ (hasFinalHornFillers_of_kanComplex _)
  let invData := ha.nonempty_inverse.some
  let inv := SSet.Edge.ofTruncated invData.1
  have hex := homotopyCategory_homMk_surjective x y
    (SSet.Truncated.HomotopyCategory.homMk inv.toTruncated ≫
      SSet.Truncated.HomotopyCategory.homMk b.toTruncated)
  let e := SSet.Edge.ofTruncated hex.choose
  let ht := compStruct_nonempty_of_homMk_fac hex.choose_spec.symm
  exact ⟨inv, SSet.Edge.CompStruct.ofTruncated invData.2.1,
    SSet.Edge.CompStruct.ofTruncated invData.2.2, e, SSet.Edge.CompStruct.ofTruncated ht.some⟩

end SerrePositivity.InfinityCategories.Kan

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.KanMappingSpanComposition (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.KanMappingSpanComposition := _root_.SerrePositivity.InfinityCategories.Kan.KanMappingSpanComposition

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.kanMappingSpanComposition (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.kanMappingSpanComposition := _root_.SerrePositivity.InfinityCategories.Kan.kanMappingSpanComposition

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.KanMappingSpanComposition._sizeOf_1 (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.KanMappingSpanComposition._sizeOf_1 := _root_.SerrePositivity.InfinityCategories.Kan.KanMappingSpanComposition._sizeOf_1

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.KanMappingSpanComposition._sizeOf_inst (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.KanMappingSpanComposition._sizeOf_inst := _root_.SerrePositivity.InfinityCategories.Kan.KanMappingSpanComposition._sizeOf_inst

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.KanMappingSpanComposition.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.KanMappingSpanComposition.casesOn := _root_.SerrePositivity.InfinityCategories.Kan.KanMappingSpanComposition.casesOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.KanMappingSpanComposition.ctorIdx (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.KanMappingSpanComposition.ctorIdx := _root_.SerrePositivity.InfinityCategories.Kan.KanMappingSpanComposition.ctorIdx

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.KanMappingSpanComposition.edge (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.KanMappingSpanComposition.edge := _root_.SerrePositivity.InfinityCategories.Kan.KanMappingSpanComposition.edge

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.KanMappingSpanComposition.inverse (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.KanMappingSpanComposition.inverse := _root_.SerrePositivity.InfinityCategories.Kan.KanMappingSpanComposition.inverse

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.KanMappingSpanComposition.inverseLeft (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.KanMappingSpanComposition.inverseLeft := _root_.SerrePositivity.InfinityCategories.Kan.KanMappingSpanComposition.inverseLeft

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.KanMappingSpanComposition.inverseRight (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.KanMappingSpanComposition.inverseRight := _root_.SerrePositivity.InfinityCategories.Kan.KanMappingSpanComposition.inverseRight

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.KanMappingSpanComposition.mk (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.KanMappingSpanComposition.mk := _root_.SerrePositivity.InfinityCategories.Kan.KanMappingSpanComposition.mk

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.KanMappingSpanComposition.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.KanMappingSpanComposition.noConfusion := _root_.SerrePositivity.InfinityCategories.Kan.KanMappingSpanComposition.noConfusion

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.KanMappingSpanComposition.noConfusionType (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.KanMappingSpanComposition.noConfusionType := _root_.SerrePositivity.InfinityCategories.Kan.KanMappingSpanComposition.noConfusionType

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.KanMappingSpanComposition.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.KanMappingSpanComposition.rec := _root_.SerrePositivity.InfinityCategories.Kan.KanMappingSpanComposition.rec

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.KanMappingSpanComposition.recOn (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.KanMappingSpanComposition.recOn := _root_.SerrePositivity.InfinityCategories.Kan.KanMappingSpanComposition.recOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.KanMappingSpanComposition.triangle (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.KanMappingSpanComposition.triangle := _root_.SerrePositivity.InfinityCategories.Kan.KanMappingSpanComposition.triangle

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.kanMappingSpanComposition._proof_1 := _root_.SerrePositivity.InfinityCategories.Kan.kanMappingSpanComposition._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.kanMappingSpanComposition._proof_2 := _root_.SerrePositivity.InfinityCategories.Kan.kanMappingSpanComposition._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.kanMappingSpanComposition._proof_3 := _root_.SerrePositivity.InfinityCategories.Kan.kanMappingSpanComposition._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.kanMappingSpanComposition._proof_4 := _root_.SerrePositivity.InfinityCategories.Kan.kanMappingSpanComposition._proof_4

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.KanMappingSpanComposition.mk._flat_ctor (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.KanMappingSpanComposition.mk._flat_ctor := _root_.SerrePositivity.InfinityCategories.Kan.KanMappingSpanComposition.mk._flat_ctor

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.KanMappingSpanComposition.mk.inj := _root_.SerrePositivity.InfinityCategories.Kan.KanMappingSpanComposition.mk.inj

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.KanMappingSpanComposition.mk.injEq := _root_.SerrePositivity.InfinityCategories.Kan.KanMappingSpanComposition.mk.injEq

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.KanMappingSpanComposition.mk.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.KanMappingSpanComposition.mk.noConfusion := _root_.SerrePositivity.InfinityCategories.Kan.KanMappingSpanComposition.mk.noConfusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.KanMappingSpanComposition.mk.sizeOf_spec := _root_.SerrePositivity.InfinityCategories.Kan.KanMappingSpanComposition.mk.sizeOf_spec
