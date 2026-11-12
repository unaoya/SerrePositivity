module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
public import Mathlib.CategoryTheory.Retract
public import Mathlib.Tactic.CrossRefAttribute

/-!
頂点の retract とその基本性質。Kerodon 8.5.1.1（Tag 03YJ）。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
open _root_.SerrePositivity.InfinityCategories

/-- 同じ二頂点のホモトピー圏内の元の retract データ。 -/
@[kerodon 03YJ]
abbrev VertexRetraction {X : SSet.{u}} (x y : X _⦋0⦌) :=
  Retract (HomotopyCategory.mk x) (HomotopyCategory.mk y)

/-- 同じ retract が指定する元の自己射は冪等。 -/
lemma VertexRetraction.idempotent {X : SSet.{u}} {x y : X _⦋0⦌}
    (s : VertexRetraction x y) : (s.r ≫ s.i) ≫ (s.r ≫ s.i) = s.r ≫ s.i := by
  simp only [Category.assoc, s.retract_assoc]

/-- 同じ元の冪等射を分裂する二つの retract の、指定射を使う頂点同型。 -/
def VertexRetraction.isoOfSameIdempotent {X : SSet.{u}} {x y z : X _⦋0⦌}
    (s : VertexRetraction x z) (t : VertexRetraction y z)
    (h : s.r ≫ s.i = t.r ≫ t.i) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso x y where
  hom := s.i ≫ t.r
  inv := t.i ≫ s.r
  hom_inv_id := by
    rw [Category.assoc, ← Category.assoc t.r, ← h]
    simp only [← Category.assoc, s.retract, Category.id_comp]
  inv_hom_id := by
    rw [Category.assoc, ← Category.assoc s.r, h]
    simp only [← Category.assoc, t.retract, Category.id_comp]

/-- 分裂包含と可換する射は、同じ元の二つの分裂からの標準射に一意に決まる。 -/
lemma VertexRetraction.hom_unique {X : SSet.{u}} {x y z : X _⦋0⦌}
    (s : VertexRetraction x z) (t : VertexRetraction y z)
    (f : HomotopyCategory.mk x ⟶ HomotopyCategory.mk y) (h : f ≫ t.i = s.i) :
    f = s.i ≫ t.r := by
  rw [← h, Category.assoc, t.retract, Category.comp_id]

/-- 元の頂点 x が元の頂点 y の retract であるという条件。 -/
@[kerodon 03YJ]
def IsVertexRetractOf {X : SSet.{u}} (x y : X _⦋0⦌) : Prop :=
  Nonempty (VertexRetraction x y)

/-- 元の頂点は自身の retract。 -/
lemma IsVertexRetractOf.refl {X : SSet.{u}} (x : X _⦋0⦌) : IsVertexRetractOf x x :=
  ⟨Retract.refl _⟩

/-- 元の同じ中間頂点を持つ二つの retract は合成できる。 -/
lemma IsVertexRetractOf.trans {X : SSet.{u}} {x y z : X _⦋0⦌}
    (h : IsVertexRetractOf x y) (k : IsVertexRetractOf y z) : IsVertexRetractOf x z :=
  ⟨h.some.trans k.some⟩

/-- 頂点同型は同じ二頂点の retract を与える。 -/
lemma IsVertexRetractOf.of_iso {X : SSet.{u}} {x y : X _⦋0⦌}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso x y) : IsVertexRetractOf x y := ⟨Retract.ofIso e⟩

/-- 元の単体的関手は、同じ頂点と射の類を持つ retract を保存する。 -/
lemma IsVertexRetractOf.map {X Y : SSet.{u}} {x y : X _⦋0⦌}
    (h : IsVertexRetractOf x y) (F : X ⟶ Y) :
    IsVertexRetractOf (F.app (Opposite.op ⦋0⦌) x) (F.app (Opposite.op ⦋0⦌) y) :=
  ⟨h.some.map (hoFunctor.map F).toFunctor⟩

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
