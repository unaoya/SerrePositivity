module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.CoherentStringEndpoints

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
