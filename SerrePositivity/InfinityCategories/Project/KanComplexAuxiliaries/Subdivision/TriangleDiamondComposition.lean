module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.TriangleDiamondTransport
public import Mathlib.AlgebraicTopology.SimplicialSet.CompStruct

/-! # 元の二単体から同じ対角辺を持つ二つの実合成三角形を回収
概要：元の全四辺を持つ二単体対を、同じ対角辺を持つ二つの合成三角形にする。
方針：元の第一二単体の対角辺の両端を単体恒等式で回収し、同じ全二単体を保持する。
規約：新しい辺・三角形の充填をしない。元の全二単体の等号を保存する。
使われ方：BF の二経路の実合成三角形と元の共通対角辺の回収。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open scoped _root_.Simplicial

/-- 指定した四辺を持ち、同じ実対角辺に合成する二つの実三角形。 -/
structure CompositionDiamond {E : SSet.{u}} {x m n z : E _⦋0⦌}
    (a : E.Edge x m) (b : E.Edge m z) (c : E.Edge x n) (d : E.Edge n z) where
  /-- 元の二経路が共有する同じ実対角辺。 -/
  diagonal : E.Edge x z
  /-- 第一経路の元の実合成三角形。 -/
  first : SSet.Edge.CompStruct a b diagonal
  /-- 第二経路の元の実合成三角形。 -/
  second : SSet.Edge.CompStruct c d diagonal

/-- 元の二単体そのものから、元の四辺と共通対角辺の実三角形対を回収する。 -/
def triangleDiamondCompositionData {E : SSet.{u}} {x m n z : E _⦋0⦌}
    (a : E.Edge x m) (b : E.Edge m z) (c : E.Edge x n) (d : E.Edge n z)
    (T : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleDiamondData E a.edge c.edge b.edge d.edge) :
    {D : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond a b c d //
      D.first.simplex = T.first ∧ D.second.simplex = T.second} := by
  have hs : E.δ 1 (E.δ 1 T.first) = x := by
    have hi := ConcreteCategory.congr_hom
      (SimplicialObject.δ_comp_δ_self E (n := 0) (i := 1)) T.first
    exact hi.trans ((congrArg (E.δ 1) T.first_lower).trans a.src_eq)
  have ht : E.δ 0 (E.δ 1 T.first) = z := by
    have hi := ConcreteCategory.congr_hom
      (SimplicialObject.δ_comp_δ_self E (n := 0) (i := 0)) T.first
    exact hi.symm.trans ((congrArg (E.δ 0) T.first_upper).trans b.tgt_eq)
  let e : E.Edge x z := ⟨E.δ 1 T.first, hs, ht⟩
  exact ⟨⟨e, SSet.Edge.CompStruct.mk T.first T.first_lower T.first_upper rfl,
    SSet.Edge.CompStruct.mk T.second T.second_lower T.second_upper T.diagonal.symm⟩, rfl, rfl⟩

/-- 四辺の表示を移しても、元の全二単体と共通対角辺を変更しない。 -/
def TriangleDiamondData.ofEq {E : SSet.{u}} {a b c d a' b' c' d' : E _⦋1⦌}
    (T : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleDiamondData E a b c d) (ha : a = a') (hb : b = b') (hc : c = c') (hd : d = d') :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleDiamondData E a' b' c' d' where
  first := T.first
  second := T.second
  first_lower := T.first_lower.trans ha
  second_lower := T.second_lower.trans hb
  first_upper := T.first_upper.trans hc
  second_upper := T.second_upper.trans hd
  diagonal := T.diagonal

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CompositionDiamond := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.triangleDiamondCompositionData (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.triangleDiamondCompositionData := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.triangleDiamondCompositionData

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond._sizeOf_1 (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.CompositionDiamond._sizeOf_1 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond._sizeOf_1

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond._sizeOf_inst (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.CompositionDiamond._sizeOf_inst := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond._sizeOf_inst

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CompositionDiamond.casesOn := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond.casesOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond.ctorIdx (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CompositionDiamond.ctorIdx := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond.ctorIdx

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond.diagonal (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CompositionDiamond.diagonal := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond.diagonal

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond.first (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CompositionDiamond.first := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond.first

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond.mk (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CompositionDiamond.mk := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond.mk

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.CompositionDiamond.noConfusion := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond.noConfusion

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond.noConfusionType (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CompositionDiamond.noConfusionType := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond.noConfusionType

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CompositionDiamond.rec := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond.rec

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond.recOn (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.CompositionDiamond.recOn := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond.recOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond.second (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CompositionDiamond.second := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond.second

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleDiamondData.ofEq (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.TriangleDiamondData.ofEq := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleDiamondData.ofEq

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.triangleDiamondCompositionData._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.triangleDiamondCompositionData._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.triangleDiamondCompositionData._proof_10 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.triangleDiamondCompositionData._proof_10

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.triangleDiamondCompositionData._proof_11 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.triangleDiamondCompositionData._proof_11

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.triangleDiamondCompositionData._proof_12 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.triangleDiamondCompositionData._proof_12

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.triangleDiamondCompositionData._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.triangleDiamondCompositionData._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.triangleDiamondCompositionData._proof_3 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.triangleDiamondCompositionData._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.triangleDiamondCompositionData._proof_4 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.triangleDiamondCompositionData._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.triangleDiamondCompositionData._proof_5 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.triangleDiamondCompositionData._proof_5

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.triangleDiamondCompositionData._proof_6 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.triangleDiamondCompositionData._proof_6

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.triangleDiamondCompositionData._proof_7 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.triangleDiamondCompositionData._proof_7

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.triangleDiamondCompositionData._proof_8 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.triangleDiamondCompositionData._proof_8

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.triangleDiamondCompositionData._proof_9 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.triangleDiamondCompositionData._proof_9

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond.mk._flat_ctor (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.CompositionDiamond.mk._flat_ctor := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond.mk._flat_ctor

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CompositionDiamond.mk.inj := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond.mk.inj

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CompositionDiamond.mk.injEq := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond.mk.injEq

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond.mk.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.CompositionDiamond.mk.noConfusion := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond.mk.noConfusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CompositionDiamond.mk.sizeOf_spec := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond.mk.sizeOf_spec

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.TriangleDiamondData.ofEq._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleDiamondData.ofEq._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.TriangleDiamondData.ofEq._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleDiamondData.ofEq._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.TriangleDiamondData.ofEq._proof_3 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleDiamondData.ofEq._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.TriangleDiamondData.ofEq._proof_4 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleDiamondData.ofEq._proof_4
