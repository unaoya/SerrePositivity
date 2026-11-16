module

public import SerrePositivity.InfinityCategories.Sheaves.CechPowerMaps
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SimplexPrefix
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.Data.Fin.Tuple.Basic

/-!
概要：Čech の左 comma に固定した根の座標を付け加える。
方針：元の有限冪の普遍性と既存の単体作用素の prefix を使う。
  文献対応：HTT 4.1.3.1、Kerodon Theorem 7.2.3.1（Tag 02NY）の comma の収縮。
規約：根は指定射 V → U。弱終性から後で選び、有限積一般を仮定しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [Category.{v} C] {U V : C}

/-- 左 comma の対象は V から指定 Čech 冪への射。 -/
abbrev CechComma (d : CategoryTheory.CechNerveData U) (V : C) :=
  CostructuredArrow d.obj.rightOp (Opposite.op V)

/-- 元の全座標の前に根を一つ付け加えた射。 -/
def cechCommaPrefixLift (d : CategoryTheory.CechNerveData U) (r : V ⟶ U)
    (a : CechComma d V) : V ⟶ d.obj.obj (Opposite.op ⦋a.left.len + 1⦌) :=
  cechPowerLift d (Fin.cons (α := fun _ : Fin (a.left.len + 2) ↦ V ⟶ U) r
    (fun i ↦ a.hom.unop ≫ d.proj a.left.len i))

/-- prefix の射影は元の座標と根を回収する。 -/
lemma cechCommaPrefixLift_proj (d : CategoryTheory.CechNerveData U) (r : V ⟶ U)
    (a : CechComma d V) (i : Fin (a.left.len + 2)) :
    cechCommaPrefixLift d r a ≫ d.proj (a.left.len + 1) i =
      Fin.cons (α := fun _ : Fin (a.left.len + 2) ↦ V ⟶ U) r
        (fun j ↦ a.hom.unop ≫ d.proj a.left.len j) i :=
  cechPowerLift_proj d _ i

/-- 元の comma の射と、根を付加した射は整合する。 -/
lemma cechCommaPrefixLift_map (d : CategoryTheory.CechNerveData U) (r : V ⟶ U)
    {a b : CechComma d V} (f : a ⟶ b) :
    cechCommaPrefixLift d r b ≫ d.obj.map (simplexPrefixMap f.left).op =
      cechCommaPrefixLift d r a := by
  apply cechPower_hom_ext d
  intro i
  rw [Category.assoc, d.proj_map, cechCommaPrefixLift_proj, cechCommaPrefixLift_proj]
  cases i using Fin.cases with
  | zero => rfl
  | succ i =>
    change b.hom.unop ≫ d.proj b.left.len (f.left.toOrderHom i) =
      a.hom.unop ≫ d.proj a.left.len i
    have hw : b.hom.unop ≫ d.obj.map f.left.op = a.hom.unop :=
      congrArg Quiver.Hom.unop f.w
    rw [← hw, Category.assoc, d.proj_map]

/-- 根の追加は同じ左 comma の自己関手になる。 -/
def cechCommaPrefix (d : CategoryTheory.CechNerveData U) (r : V ⟶ U) :
    CechComma d V ⥤ CechComma d V where
  obj a := CostructuredArrow.mk (cechCommaPrefixLift d r a).op
  map f := CostructuredArrow.homMk (simplexPrefixMap f.left) (by
    apply Quiver.Hom.unop_inj
    exact cechCommaPrefixLift_map d r f)
  map_id a := by
    apply CostructuredArrow.hom_ext
    exact simplexPrefixMap_id a.left
  map_comp f g := by
    apply CostructuredArrow.hom_ext
    exact simplexPrefixMap_comp f.left g.left

end SerrePositivity.InfinityCategories.Sheaves
