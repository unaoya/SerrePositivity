module

public import SerrePositivity.InfinityCategories.Core.Equivalence
public import Mathlib.CategoryTheory.Retract
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：頂点の retract と、その元の ∞ 圏内の retract 閉包を定義する。
方針：ホモトピー圏の元の頂点間の射と分裂等式を使用する。
規約：同じ頂点を保持し、coherent な分裂の存在との同値は別に証明する。
使われ方：HTT 5.1.4.2 の前層内の retract 閉包の構成。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Idempotent

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
    (h : s.r ≫ s.i = t.r ≫ t.i) : VertexIso x y where
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
    (e : VertexIso x y) : IsVertexRetractOf x y := ⟨Retract.ofIso e⟩

/-- 元の単体的関手は、同じ頂点と射の類を持つ retract を保存する。 -/
lemma IsVertexRetractOf.map {X Y : SSet.{u}} {x y : X _⦋0⦌}
    (h : IsVertexRetractOf x y) (F : X ⟶ Y) :
    IsVertexRetractOf (F.app (Opposite.op ⦋0⦌) x) (F.app (Opposite.op ⦋0⦌) y) :=
  ⟨h.some.map (hoFunctor.map F).toFunctor⟩

/-- 元の頂点条件の、同じ ∞ 圏内での retract 閉包。 -/
def retractClosure {X : SSet.{u}} (P : X _⦋0⦌ → Prop) (x : X _⦋0⦌) : Prop :=
  ∃ y, P y ∧ IsVertexRetractOf x y

/-- retract 閉包は元の対象条件を含む。 -/
lemma mem_retractClosure {X : SSet.{u}} {P : X _⦋0⦌ → Prop} {x : X _⦋0⦌}
    (h : P x) : retractClosure P x := ⟨x, h, IsVertexRetractOf.refl x⟩

/-- 元の条件の包含は、その retract 閉包の包含を与える。 -/
lemma retractClosure_mono {X : SSet.{u}} {P Q : X _⦋0⦌ → Prop}
    (h : ∀ x, P x → Q x) {x : X _⦋0⦌} : retractClosure P x → retractClosure Q x := by
  rintro ⟨y, hy, hxy⟩
  exact ⟨y, h y hy, hxy⟩

/-- 元の retract 閉包は retract に関して閉じている。 -/
lemma retractClosure_of_retract {X : SSet.{u}} {P : X _⦋0⦌ → Prop}
    {x y : X _⦋0⦌} (h : IsVertexRetractOf x y) (hy : retractClosure P y) :
    retractClosure P x := by
  obtain ⟨z, hz, hyz⟩ := hy
  exact ⟨z, hz, h.trans hyz⟩

/-- retract 閉包は冪等。 -/
lemma retractClosure_idempotent {X : SSet.{u}} (P : X _⦋0⦌ → Prop) (x : X _⦋0⦌) :
    retractClosure (retractClosure P) x ↔ retractClosure P x := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact retractClosure_of_retract hxy hy
  · exact mem_retractClosure

/-- 元の retract 閉包の所属は元の頂点同型で不変。 -/
lemma retractClosure_iff_of_iso {X : SSet.{u}} (P : X _⦋0⦌ → Prop)
    {x y : X _⦋0⦌} (e : VertexIso x y) : retractClosure P x ↔ retractClosure P y := by
  constructor
  · exact retractClosure_of_retract (IsVertexRetractOf.of_iso e.symm)
  · exact retractClosure_of_retract (IsVertexRetractOf.of_iso e)

end SerrePositivity.InfinityCategories.F2.Idempotent
