module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentStringEndpoints

/-! # 元の射を合成とする有限合成列とその精密化の圏
概要：同じ元の射を長辺に持つ全合成列と、両端を保つ再添字を一つの圏にする。
方針：nerve の元の長辺の等式をデータとして保ち、単体作用の合成で圏の則を証明する。
規約：恒等の挿入と長さ零の列を除外しない。各列の辺や合成は選び直さない。
使われ方：元の高次 K prism の全合成列を同じパラメータへ束ねる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open scoped _root_.Simplicial
variable {I : Type u} [SmallCategory I] {x y : I}

/-- 元の射をそのまま長辺に持つ、任意の有限合成列。 -/
structure CoherentArrowString (f : x ⟶ y) : Type u where
  /-- 元の合成列の長さ。 -/
  length : ℕ
  /-- 元の高次 nerve 単体としての全合成列。 -/
  chain : (nerve I) _⦋length⦌
  /-- 長辺は指定した元の射そのもの。 -/
  long_edge : (nerve I).map (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentStringEndpointMap length).op chain = (nerve.edgeMk f).edge

/-- 両端と元の合成列そのものを保つ精密化。 -/
structure CoherentArrowStringHom {f : x ⟶ y} (s t : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f) : Type u where
  /-- 元の単体圏の再添字。 -/
  map : ⦋s.length⦌ ⟶ ⦋t.length⦌
  /-- 元の始点を保持する。 -/
  first : map.toOrderHom 0 = 0
  /-- 元の終点を保持する。 -/
  last : map.toOrderHom (Fin.last s.length) = Fin.last t.length
  /-- 元の全合成列を高次単体として保持する。 -/
  comm : (nerve I).map map.op t.chain = s.chain

/-- 再添字が同じなら、元の合成列の精密化は同じ。 -/
@[ext]
lemma CoherentArrowStringHom.ext {f : x ⟶ y} {s t : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f}
    {a b : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowStringHom s t} (h : a.map = b.map) : a = b := by
  cases a
  cases b
  cases h
  rfl

/-- 元の射の有限合成列と全ての両端固定の精密化の圏。 -/
instance coherentArrowString_category (f : x ⟶ y) : SmallCategory (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f) where
  Hom := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowStringHom
  id s :=
    { map := 𝟙 _
      first := rfl
      last := rfl
      comm := by simp }
  comp a b :=
    { map := a.map ≫ b.map
      first := by change b.map.toOrderHom (a.map.toOrderHom 0) = 0; rw [a.first, b.first]
      last := by
        change b.map.toOrderHom (a.map.toOrderHom (Fin.last _)) = _
        rw [a.last, b.last]
      comm := by
        rw [op_comp, CategoryTheory.Functor.map_comp_apply, b.comm, a.comm] }
  id_comp a := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowStringHom.ext (Category.id_comp _)
  comp_id a := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowStringHom.ext (Category.comp_id _)
  assoc a b c := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowStringHom.ext (Category.assoc _ _ _)

/-- 元の長辺の等式から、合成列の始点を厳密に回収する。 -/
lemma coherentArrowString_first {f : x ⟶ y} (s : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f) :
    s.chain.obj 0 = x := by
  have h := congrArg (fun z : (nerve I) _⦋1⦌ => z.obj 0) s.long_edge
  change s.chain.obj ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentStringEndpointMap s.length).toOrderHom 0) = x at h
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentStringEndpointMap_first] at h
  exact h

/-- 元の長辺の等式から、合成列の終点を厳密に回収する。 -/
lemma coherentArrowString_last {f : x ⟶ y} (s : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f) :
    s.chain.obj (Fin.last s.length) = y := by
  have h := congrArg (fun z : (nerve I) _⦋1⦌ => z.obj 1) s.long_edge
  change s.chain.obj ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentStringEndpointMap s.length).toOrderHom 1) = y at h
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentStringEndpointMap_last] at h
  exact h

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CoherentArrowString := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowStringHom (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CoherentArrowStringHom := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowStringHom

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentArrowString_category (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentArrowString_category := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentArrowString_category

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentArrowString_first := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentArrowString_first

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentArrowString_last := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentArrowString_last

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString._sizeOf_1 (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.CoherentArrowString._sizeOf_1 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString._sizeOf_1

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString._sizeOf_inst (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.CoherentArrowString._sizeOf_inst := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString._sizeOf_inst

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CoherentArrowString.casesOn := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString.casesOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString.chain (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CoherentArrowString.chain := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString.chain

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString.ctorIdx (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CoherentArrowString.ctorIdx := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString.ctorIdx

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString.length (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CoherentArrowString.length := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString.length

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CoherentArrowString.long_edge := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString.long_edge

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString.mk (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CoherentArrowString.mk := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString.mk

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.CoherentArrowString.noConfusion := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString.noConfusion

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString.noConfusionType (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CoherentArrowString.noConfusionType := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString.noConfusionType

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CoherentArrowString.rec := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString.rec

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString.recOn (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.CoherentArrowString.recOn := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString.recOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowStringHom._sizeOf_1 (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.CoherentArrowStringHom._sizeOf_1 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowStringHom._sizeOf_1

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowStringHom._sizeOf_inst (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.CoherentArrowStringHom._sizeOf_inst := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowStringHom._sizeOf_inst

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowStringHom.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CoherentArrowStringHom.casesOn := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowStringHom.casesOn

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CoherentArrowStringHom.comm := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowStringHom.comm

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowStringHom.ctorIdx (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CoherentArrowStringHom.ctorIdx := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowStringHom.ctorIdx

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CoherentArrowStringHom.ext := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowStringHom.ext

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CoherentArrowStringHom.ext_iff := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowStringHom.ext_iff

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CoherentArrowStringHom.first := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowStringHom.first

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CoherentArrowStringHom.last := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowStringHom.last

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowStringHom.map (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CoherentArrowStringHom.map := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowStringHom.map

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowStringHom.mk (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CoherentArrowStringHom.mk := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowStringHom.mk

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowStringHom.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.CoherentArrowStringHom.noConfusion := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowStringHom.noConfusion

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowStringHom.noConfusionType (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CoherentArrowStringHom.noConfusionType := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowStringHom.noConfusionType

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowStringHom.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CoherentArrowStringHom.rec := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowStringHom.rec

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowStringHom.recOn (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.CoherentArrowStringHom.recOn := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowStringHom.recOn

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentArrowString_category._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentArrowString_category._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentArrowString_category._proof_10 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentArrowString_category._proof_10

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentArrowString_category._proof_11 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentArrowString_category._proof_11

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentArrowString_category._proof_12 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentArrowString_category._proof_12

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentArrowString_category._proof_13 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentArrowString_category._proof_13

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentArrowString_category._proof_14 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentArrowString_category._proof_14

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentArrowString_category._proof_15 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentArrowString_category._proof_15

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentArrowString_category._proof_16 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentArrowString_category._proof_16

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentArrowString_category._proof_17 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentArrowString_category._proof_17

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentArrowString_category._proof_18 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentArrowString_category._proof_18

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentArrowString_category._proof_19 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentArrowString_category._proof_19

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentArrowString_category._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentArrowString_category._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentArrowString_category._proof_20 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentArrowString_category._proof_20

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentArrowString_category._proof_21 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentArrowString_category._proof_21

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentArrowString_category._proof_22 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentArrowString_category._proof_22

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentArrowString_category._proof_3 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentArrowString_category._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentArrowString_category._proof_4 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentArrowString_category._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentArrowString_category._proof_5 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentArrowString_category._proof_5

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentArrowString_category._proof_6 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentArrowString_category._proof_6

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentArrowString_category._proof_7 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentArrowString_category._proof_7

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentArrowString_category._proof_8 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentArrowString_category._proof_8

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentArrowString_category._proof_9 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentArrowString_category._proof_9

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString.mk._flat_ctor (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.CoherentArrowString.mk._flat_ctor := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString.mk._flat_ctor

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CoherentArrowString.mk.inj := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString.mk.inj

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CoherentArrowString.mk.injEq := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString.mk.injEq

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString.mk.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.CoherentArrowString.mk.noConfusion := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString.mk.noConfusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CoherentArrowString.mk.sizeOf_spec := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString.mk.sizeOf_spec

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowStringHom.mk._flat_ctor (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.CoherentArrowStringHom.mk._flat_ctor := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowStringHom.mk._flat_ctor

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CoherentArrowStringHom.mk.inj := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowStringHom.mk.inj

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CoherentArrowStringHom.mk.injEq := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowStringHom.mk.injEq

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowStringHom.mk.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.CoherentArrowStringHom.mk.noConfusion := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowStringHom.mk.noConfusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CoherentArrowStringHom.mk.sizeOf_spec := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowStringHom.mk.sizeOf_spec
