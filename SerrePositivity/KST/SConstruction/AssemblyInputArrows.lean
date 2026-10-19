module
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Products.Basic

/-! # 入力の両側への合成を記録する射の圏
概要：射 f を前合成 a と後合成 b で a ≫ f ≫ b へ移す圏を構成する。
方針：Hom の両変数関手の category of elements を使う。
規約：前合成の向きは反変、後合成の向きは共変。
使われ方：全入力射列にわたる混合選択空間の厳密な図式。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Opposite

/-- 前合成・後合成で動く通常の Hom の両変数関手。 -/
def assemblyHomBifunctor (J : Type v) [Category.{w} J] : Jᵒᵖ × J ⥤ Type w where
  obj x := unop x.1 ⟶ x.2
  map h := ↾fun f => h.1.unop ≫ f ≫ h.2
  map_id x := by
    apply ConcreteCategory.hom_ext
    intro f
    simp
  map_comp h k := by
    apply ConcreteCategory.hom_ext
    intro f
    simp [Category.assoc]

/-- 両側への合成を射とする、入力の射の圏。 -/
abbrev AssemblyInputArrow (J : Type v) [Category.{w} J] := (assemblyHomBifunctor J).Elements

/-- 入力射の始域。 -/
abbrev assemblyArrowSource {J : Type v} [Category.{w} J] (x : AssemblyInputArrow J) :=
  unop x.obj.1

/-- 入力射の終域。 -/
abbrev assemblyArrowTarget {J : Type v} [Category.{w} J] (x : AssemblyInputArrow J) := x.obj.2

/-- 圏の対象として保持する元の入力射。 -/
abbrev assemblyArrowHom {J : Type v} [Category.{w} J] (x : AssemblyInputArrow J) :
    assemblyArrowSource x ⟶ assemblyArrowTarget x := x.val

/-- 両側合成の前合成部分。 -/
abbrev assemblyArrowPre {J : Type v} [Category.{w} J] {x y : AssemblyInputArrow J} (h : x ⟶ y) :
    assemblyArrowSource y ⟶ assemblyArrowSource x := h.hom.1.unop

/-- 両側合成の後合成部分。 -/
abbrev assemblyArrowPost {J : Type v} [Category.{w} J] {x y : AssemblyInputArrow J} (h : x ⟶ y) :
    assemblyArrowTarget x ⟶ assemblyArrowTarget y := h.hom.2

/-- 射の圏の可換条件は元の入力射の両側合成。 -/
lemma assemblyArrow_comm {J : Type v} [Category.{w} J] {x y : AssemblyInputArrow J} (h : x ⟶ y) :
    assemblyArrowPre h ≫ assemblyArrowHom x ≫ assemblyArrowPost h = assemblyArrowHom y :=
  h.map_val

/-- 通常の射を入力射の圏の対象とする。 -/
def assemblyArrowMk {J : Type v} [Category.{w} J] {X Y : J} (f : X ⟶ Y) : AssemblyInputArrow J :=
  (assemblyHomBifunctor J).elementsMk (op X, Y) f

/-- 前後の射と可換条件から入力射の圏の射を作る。 -/
def assemblyArrowMap {J : Type v} [Category.{w} J] {x y : AssemblyInputArrow J}
    (a : assemblyArrowSource y ⟶ assemblyArrowSource x)
    (b : assemblyArrowTarget x ⟶ assemblyArrowTarget y)
    (h : a ≫ assemblyArrowHom x ≫ b = assemblyArrowHom y) : x ⟶ y :=
  ⟨(a.op, b), h⟩

/-- 恒等の前合成部分。 -/
lemma assemblyArrowPre_id {J : Type v} [Category.{w} J] (x : AssemblyInputArrow J) :
    assemblyArrowPre (𝟙 x) = 𝟙 (assemblyArrowSource x) := rfl

/-- 恒等の後合成部分。 -/
lemma assemblyArrowPost_id {J : Type v} [Category.{w} J] (x : AssemblyInputArrow J) :
    assemblyArrowPost (𝟙 x) = 𝟙 (assemblyArrowTarget x) := rfl

/-- 合成の前合成部分は逆の順序で合成される。 -/
lemma assemblyArrowPre_comp {J : Type v} [Category.{w} J]
    {x y z : AssemblyInputArrow J} (h : x ⟶ y) (k : y ⟶ z) :
    assemblyArrowPre (h ≫ k) = assemblyArrowPre k ≫ assemblyArrowPre h := rfl

/-- 合成の後合成部分は元の順序で合成される。 -/
lemma assemblyArrowPost_comp {J : Type v} [Category.{w} J]
    {x y z : AssemblyInputArrow J} (h : x ⟶ y) (k : y ⟶ z) :
    assemblyArrowPost (h ≫ k) = assemblyArrowPost h ≫ assemblyArrowPost k := rfl

end SerrePositivity.KST.SConstruction
