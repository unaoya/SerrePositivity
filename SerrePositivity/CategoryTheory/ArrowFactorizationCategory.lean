module

public import SerrePositivity.CategoryTheory.AnchoredChain
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

/-!
# 固定した射の因子分解圏で終域側の自明な因子分解が終対象となる

## 概要
固定した射の因子分解圏で終域側の自明な因子分解が終対象となる。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
中間対象と二つの因子を明示し、射には左右の三角形の可換性を要求する。
恒等・合成・移送をこのデータ上で定義し、成分の一意性から法則を導く。

## 規約と注意
圏・対象・射の宇宙と必要な極限の仮定は各宣言に従う。
表示された圏や比較射を、局所化後の同型だけで置き換えない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はS-構成に現れる圏のnerve、射列、図式間の自然なホモトピーに利用できる。
[棚卸し m0007][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../formalization-plans/k-theory-generalization-inventory.md#m0007
[plan]: ../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The category of actual factorizations of a fixed arrow

Morphisms commute with both external legs. The identity factorizations
at the source and target are initial and terminal, respectively.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.ArrowFactorization
variable {D : Type u} [Category.{v} D] {Y V : D} {g : Y ⟶ V}

structure Hom (a b : ArrowFactorization g) where
  hom : a.middle ⟶ b.middle
  left_comm : a.left ≫ hom = b.left
  right_comm : hom ≫ b.right = a.right

@[ext]
lemma Hom.ext {a b : ArrowFactorization g} {f h : Hom a b} (e : f.hom = h.hom) : f = h := by
  cases f
  cases h
  cases e
  rfl

instance : Category.{v} (ArrowFactorization g) where
  Hom := Hom
  id a := ⟨𝟙 a.middle, by simp, by simp⟩
  comp f h := ⟨f.hom ≫ h.hom, by rw [← Category.assoc, f.left_comm, h.left_comm],
    by rw [Category.assoc, h.right_comm, f.right_comm]⟩
  id_comp f := Hom.ext (Category.id_comp f.hom)
  comp_id f := Hom.ext (Category.comp_id f.hom)
  assoc f h k := Hom.ext (Category.assoc f.hom h.hom k.hom)

@[reassoc (attr := simp)]
lemma left_comp {a b : ArrowFactorization g} (f : a ⟶ b) : a.left ≫ f.hom = b.left := f.left_comm

@[reassoc (attr := simp)]
lemma comp_right {a b : ArrowFactorization g} (f : a ⟶ b) :
    f.hom ≫ b.right = a.right := f.right_comm

@[simp]
lemma id_hom (a : ArrowFactorization g) : (𝟙 a : a ⟶ a).hom = 𝟙 a.middle := rfl

@[simp]
lemma comp_hom {a b c : ArrowFactorization g} (f : a ⟶ b) (h : b ⟶ c) :
    (f ≫ h).hom = f.hom ≫ h.hom := rfl

@[simp]
lemma eqToHom_hom {a b : ArrowFactorization g} (h : a = b) :
    (eqToHom h).hom = eqToHom (congrArg ArrowFactorization.middle h) := by cases h; rfl

lemma eta (a : ArrowFactorization g) :
    ArrowFactorization.mk a.middle a.left a.right a.fac = a := by cases a; rfl

variable (g)

def forget : ArrowFactorization g ⥤ D where
  obj a := a.middle
  map f := f.hom

def source : ArrowFactorization g := ⟨Y, 𝟙 Y, g, by simp⟩
def target : ArrowFactorization g := ⟨V, g, 𝟙 V, by simp⟩

def fromSource (a : ArrowFactorization g) : source g ⟶ a :=
  ⟨a.left, by simp [source], a.fac⟩

def toTarget (a : ArrowFactorization g) : a ⟶ target g :=
  ⟨a.right, a.fac, by simp [target]⟩

def source_isInitial : IsInitial (source g) :=
  IsInitial.ofUniqueHom (fromSource g) (fun a f => Hom.ext (by
    change f.hom = a.left
    simpa only [source, Category.id_comp] using f.left_comm))

/-- 固定した射の因子分解圏で終域側の自明な因子分解が終対象となる。

圏・対象・射の宇宙と必要な極限の仮定は各宣言に従う。
中間対象と二つの因子を明示し、射には左右の三角形の可換性を要求する。
恒等・合成・移送をこのデータ上で定義し、成分の一意性から法則を導く。
-/
def target_isTerminal : IsTerminal (target g) :=
  IsTerminal.ofUniqueHom (toTarget g) (fun a f => Hom.ext (by
    change f.hom = a.right
    simpa only [target, Category.comp_id] using f.right_comm))

def fromSourceNatTrans : (Functor.const (ArrowFactorization g)).obj (source g) ⟶ 𝟭 _ where
  app := fromSource g
  naturality {_ _} _ := (source_isInitial g).hom_ext _ _

def toTargetNatTrans : 𝟭 (ArrowFactorization g) ⟶ (Functor.const _).obj (target g) where
  app := toTarget g
  naturality {_ _} _ := (target_isTerminal g).hom_ext _ _

end SerrePositivity.ArrowFactorization
