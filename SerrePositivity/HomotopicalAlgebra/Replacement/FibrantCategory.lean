module

public import Mathlib.AlgebraicTopology.ModelCategory.Bifibrant
public import Mathlib.AlgebraicTopology.ModelCategory.Basic

/-!
# fibrant置換の圏で基底の弱同値を持ち上げた比較射も弱同値となる

## 概要
fibrant置換の圏で基底の弱同値を持ち上げた比較射も弱同値となる。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
指定された境界と基底から可換正方形を作り、その持ち上げ性を使う。
元の指定部分を保つ等式は、対角射の二つの分解等式から確認する。

## 規約と注意
モデル構造と射クラスの一致を要求する入口では、その指定データを仮定する。
このファイルがHT-KQの引用モデルを自動的に選ぶとは解釈しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。
[棚卸し m0337][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0337
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Actual fibrant replacements and all commuting comparison maps

Objects and lifts use ordinary model factorization. The full projection to
base objects is not asserted to have a strict functorial section.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.ModelReplacement

structure FibrantReplacementObject (C : Type u) [Category.{v} C] [ModelCategory C] where
  base : C
  obj : C
  inclusion : base ⟶ obj
  trivial : trivialCofibrations C inclusion
  fibrant : IsFibrant obj

namespace FibrantReplacementObject
variable {C : Type u} [Category.{v} C] [ModelCategory C]

instance (X : FibrantReplacementObject C) : IsFibrant X.obj := X.fibrant
instance (X : FibrantReplacementObject C) : Cofibration X.inclusion := ⟨X.trivial.1⟩
instance (X : FibrantReplacementObject C) : WeakEquivalence X.inclusion := ⟨X.trivial.2⟩

@[ext]
structure Hom (X Y : FibrantReplacementObject C) where
  base : X.base ⟶ Y.base
  map : X.obj ⟶ Y.obj
  under : X.inclusion ≫ map = base ≫ Y.inclusion

instance : Category (FibrantReplacementObject C) where
  Hom := Hom
  id X := ⟨𝟙 _, 𝟙 _, by simp⟩
  comp f g := ⟨f.base ≫ g.base, f.map ≫ g.map, by
    rw [← Category.assoc, f.under, Category.assoc, g.under, Category.assoc]⟩
  id_comp f := by ext <;> simp
  comp_id f := by ext <;> simp
  assoc f g h := by ext <;> simp only [Category.assoc]

def projection : FibrantReplacementObject C ⥤ C where
  obj X := X.base
  map f := f.base

def targets : FibrantReplacementObject C ⥤ C where
  obj X := X.obj
  map f := f.map

def fibrantTargets : FibrantReplacementObject C ⥤ FibrantObject C where
  obj X := FibrantObject.mk X.obj
  map f := ⟨f.map⟩

/-- A fibrant object is presented by its identity, functorially on actual fibrant maps. -/
def fromFibrant : FibrantObject C ⥤ FibrantReplacementObject C where
  obj X := ⟨X.obj, X.obj, 𝟙 _, (trivialCofibrations C).id_mem _, inferInstance⟩
  map f := ⟨f.hom, f.hom, by simp⟩

/-- Every presentation compares to the identity presentation of its actual fibrant target. -/
def toIdentityPresentation : 𝟭 (FibrantReplacementObject C) ⟶ fibrantTargets ⋙ fromFibrant where
  app X := ⟨X.inclusion, 𝟙 _, by change X.inclusion ≫ 𝟙 _ = X.inclusion ≫ 𝟙 _; rfl⟩
  naturality {_ _} f := by
    apply Hom.ext
    · exact f.under.symm
    · change f.map ≫ 𝟙 _ = 𝟙 _ ≫ f.map
      simp

def inclusionNatTrans : projection (C := C) ⟶ targets where
  app X := X.inclusion
  naturality {_ _} f := f.under.symm

/-- Factor only the terminal map of this object; this is an object choice. -/
def ofObject (X : C) : FibrantReplacementObject C := by
  let d := MorphismProperty.factorizationData
    (trivialCofibrations C) (fibrations C) (terminal.from X)
  exact ⟨X, d.Z, d.i, d.hi,
    (isFibrant_iff_of_isTerminal d.p terminalIsTerminal).mpr ⟨d.hp⟩⟩

@[simp]
lemma ofObject_base (X : C) : (ofObject X).base = X := rfl

/-- A trivial-cofibration lifting square supplies each actual comparison separately. -/
def liftBase {X Y : FibrantReplacementObject C} (f : X.base ⟶ Y.base) : X ⟶ Y := by
  let sq : CommSq (f ≫ Y.inclusion) X.inclusion (terminal.from Y.obj)
      (terminal.from X.obj) := ⟨by apply terminal.hom_ext⟩
  exact ⟨f, sq.lift, sq.fac_left⟩

@[simp]
lemma liftBase_base {X Y : FibrantReplacementObject C} (f : X.base ⟶ Y.base) :
    (liftBase f).base = f := rfl

instance : (projection (C := C)).Full where
  map_surjective f := ⟨liftBase f, rfl⟩

/-- Two-out-of-three transfers weak equivalences between base and actual fibrant targets. -/
lemma map_weakEquivalence_iff {X Y : FibrantReplacementObject C} (f : X ⟶ Y) :
    weakEquivalences C f.map ↔ weakEquivalences C f.base := by
  constructor
  · intro h
    exact (weakEquivalences C).of_postcomp _ _ Y.trivial.2
      (f.under ▸ (weakEquivalences C).comp_mem _ _ X.trivial.2 h)
  · intro h
    exact (weakEquivalences C).of_precomp _ _ X.trivial.2
      (f.under.symm ▸ (weakEquivalences C).comp_mem _ _ h Y.trivial.2)

/-- fibrant置換の圏で基底の弱同値を持ち上げた比較射も弱同値となる。

モデル構造と射クラスの一致を要求する入口では、その指定データを仮定する。
指定された境界と基底から可換正方形を作り、その持ち上げ性を使う。
元の指定部分を保つ等式は、対角射の二つの分解等式から確認する。
-/
lemma liftBase_weakEquivalence {X Y : FibrantReplacementObject C}
    (f : X.base ⟶ Y.base) (hf : weakEquivalences C f) :
    weakEquivalences C (liftBase (X := X) (Y := Y) f).map :=
  (map_weakEquivalence_iff _).mpr hf

end FibrantReplacementObject
end SerrePositivity.ModelReplacement
