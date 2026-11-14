module

public import SerrePositivity.Archive.KST.DescentConditional.AugmentedCechSpaces
public import Mathlib.AlgebraicTopology.CechNerve
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits

/-!
# 有限被覆族の Čech 図式

## 概要
有限被覆族の各座標の引き戻しを元の前層で写し、値域の有限積を取る実際の余単体図式を構成する。

## 方針
各添字の列の wide pullback と、単調写像に沿う指定射影から全ての面射・退化射を作る。

## 規約
非交和の前層の値を成分の積と同一視しない。空の被覆族では各段は値域の終対象となる。

## 使われ方
論文 公理 (1)、補題 3.2・3.3 の Zariski Čech 降下。τ 位相の層論を Čech 計算で置換する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v w t z

open CategoryTheory CategoryTheory.Limits Opposite

namespace SerrePositivity.KST.Descent

variable {C : Type u} [Category.{v} C] [HasFiniteLimits C]
  {ι : Type z} {Y : C} (X : ι → C) (cover : ∀ i, X i ⟶ Y)

/-- 概要：有限被覆族の指定添字の列に対する実際の Čech 段（公理 (1)）。
方針：各座標の異なる対象を同じ基底上で wide pullback にする。
規約：同じ成分を何度も選んでもよい。使われ方：被覆族の値域の積の各項。 -/
abbrev familyCechTerm (n : SimplexCategory) (a : Fin (n.len + 1) → ι) : C :=
  widePullback Y (fun j ↦ X (a j)) (fun j ↦ cover (a j))

/-- 概要：単体射に沿う被覆族 Čech 段の指定幾何射（公理 (1)）。
方針：同じ基底射と指定座標の射影で wide pullback へ持ち上げる。
規約：添字の列も同じ単体射で制限。使われ方：余単体空間図式の全射。 -/
def familyCechMap {n m : SimplexCategory} (f : n ⟶ m) (a : Fin (m.len + 1) → ι) :
    familyCechTerm X cover m a ⟶ familyCechTerm X cover n (fun j ↦ a (f.toOrderHom j)) :=
  WidePullback.lift (WidePullback.base (fun j ↦ cover (a j)))
    (fun j ↦ WidePullback.π (fun j ↦ cover (a j)) (f.toOrderHom j)) (by simp)

/-- 概要：恒等単体射の被覆族 Čech 射は恒等（公理 (1)）。
方針：全ての指定射影で検査する。
規約：幾何の射の厳密な等式。使われ方：余単体図式の恒等法則。 -/
theorem familyCechMap_id (n : SimplexCategory) (a : Fin (n.len + 1) → ι) :
    familyCechMap X cover (𝟙 n) a = 𝟙 (familyCechTerm X cover n a) := by
  apply WidePullback.hom_ext <;> simp [familyCechMap]

/-- 概要：合成単体射の被覆族 Čech 射は逆順に合成（公理 (1)）。
方針：基底射と各座標の lift の式を比較する。
規約：添字の列の制限も合成で一致。使われ方：前層の反変合成と余単体図式の合成法則。 -/
theorem familyCechMap_comp {n m l : SimplexCategory} (f : n ⟶ m) (g : m ⟶ l)
    (a : Fin (l.len + 1) → ι) :
    familyCechMap X cover (f ≫ g) a =
      familyCechMap X cover g a ≫
        familyCechMap X cover f (fun j ↦ a (g.toOrderHom j)) := by
  apply WidePullback.hom_ext <;> simp [familyCechMap]

variable [Finite ι] {V : Type w} [Category.{t} V] [HasFiniteProducts V] (F : Cᵒᵖ ⥤ V)

/-- 概要：被覆族の各 Čech 段の値の有限積（公理 (1)）。
方針：全ての添字の列の引き戻しの前層の値を積にする。
規約：元の非交和上の前層の値と同一視しない。使われ方：実際の被覆族の Čech 降下。 -/
def familyCechValue (n : SimplexCategory) : V :=
  ∏ᶜ fun a : Fin (n.len + 1) → ι ↦ F.obj (op (familyCechTerm X cover n a))

/-- 概要：被覆族 Čech 値の単体射に沿う実際の射（公理 (1)）。
方針：指定座標の積射影の後に元の前層で幾何射を引き戻す。
規約：全ての添字の列に同じ規則を使う。使われ方：被覆族の余単体図式。 -/
def familyCechValueMap {n m : SimplexCategory} (f : n ⟶ m) :
    familyCechValue X cover F n ⟶ familyCechValue X cover F m :=
  Pi.lift fun a ↦
    Pi.π (fun b ↦ F.obj (op (familyCechTerm X cover n b))) (fun j ↦ a (f.toOrderHom j)) ≫
      F.map (familyCechMap X cover f a).op

/-- 概要：有限被覆族と元の前層の実際の余単体 Čech 図式（公理 (1)）。
方針：各積射影で幾何の恒等・合成法則と元の前層の関手性を使う。
規約：被覆族の全ての面射・退化射を保持。使われ方：実際のホモトピー極限の入力。 -/
def familyCechDiagram : SimplexCategory ⥤ V where
  obj := familyCechValue X cover F
  map f := familyCechValueMap X cover F f
  map_id n := by
    apply Pi.hom_ext
    intro a
    simp [familyCechValueMap, familyCechMap_id]
  map_comp f g := by
    apply Pi.hom_ext
    intro a
    simp only [familyCechValueMap, Category.assoc, Pi.lift_comp_π]
    rw [← Category.assoc, Pi.lift_comp_π, Category.assoc, ← F.map_comp, ← op_comp,
      ← familyCechMap_comp]
    rfl

/-- 概要：元の基底の値から被覆族の各段への指定増強（公理 (1)）。
方針：各列の wide pullback の基底射を元の前層で引き戻して積へ持ち上げる。
規約：任意の比較射の選択ではない。使われ方：被覆族の実際の指定降下。 -/
def familyCechAugmentation :
    (Functor.const SimplexCategory).obj (F.obj (op Y)) ⟶ familyCechDiagram X cover F where
  app n := Pi.lift fun a ↦ F.map (WidePullback.base (fun j ↦ cover (a j))).op
  naturality {n m} f := by
    apply Pi.hom_ext
    intro a
    simp only [Category.assoc, Pi.lift_comp_π, familyCechDiagram,
      familyCechValueMap]
    rw [← Category.assoc, Pi.lift_comp_π, ← F.map_comp, ← op_comp]
    have he : familyCechMap X cover f a ≫
        WidePullback.base (fun j : Fin (n.len + 1) ↦ cover (a (f.toOrderHom j))) =
      WidePullback.base (fun j : Fin (m.len + 1) ↦ cover (a j)) :=
      WidePullback.lift_base _ _ _ _
    exact (Category.id_comp _).trans (congrArg F.map (congrArg Quiver.Hom.op he.symm))

end SerrePositivity.KST.Descent
