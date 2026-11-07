module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# 余単体的可換代数とその台加群

## 概要
固定した係数環の下の余単体的可換環を、その係数環上の余単体的加群として読む。

## 方針
各項の係数準同型から加群構造を作り、自然性で構造射の線形性を示す。

## 規約
全次数で共通の係数環を使う。

## 使われ方
交代余面複体、Bockstein、Čech–Alexander 模型。
-/

@[expose] public section

universe u

open CategoryTheory

namespace SerrePositivity.Cosimplicial

/-- 概要：固定した可換環上の余単体的可換代数。
方針：係数環の下の可換環の圏に値を取る関手。
規約：構造射は係数環を保つ。
使われ方：Čech–Alexander 模型と分冪 Čech 模型。 -/
abbrev CosimplicialAlgebra (k : Type u) [CommRing k] :=
  CosimplicialObject (Under (CommRingCat.of k))

/-- 概要：係数環からの自然な射を持つ余単体的可換環の台加群。
方針：各項で係数準同型から加群構造を作る。
規約：自然変換は定数図式を始域とする。
使われ方：余単体的な商の短完全列と Bockstein。 -/
def toModules (k : Type u) [CommRing k] (C : CosimplicialObject CommRingCat.{u})
    (ι : (Functor.const SimplexCategory).obj (CommRingCat.of k) ⟶ C) :
    CosimplicialObject (ModuleCat.{u} k) where
  obj n := @ModuleCat.of k _ (C.obj n) _ (ι.app n).hom.toAlgebra.toModule
  map {m n} θ := by
    letI : Module k (C.obj m) := (ι.app m).hom.toAlgebra.toModule
    letI : Module k (C.obj n) := (ι.app n).hom.toAlgebra.toModule
    exact ModuleCat.ofHom {
      toFun := (C.map θ).hom
      map_add' := (C.map θ).hom.map_add
      map_smul' := fun r x => by
        change (C.map θ).hom ((ι.app m).hom r * x) = (ι.app n).hom r * (C.map θ).hom x
        rw [map_mul]
        have h : ι.app n = ι.app m ≫ C.map θ := by simpa using ι.naturality θ
        exact congrArg (fun a : C.obj n => a * (C.map θ).hom x)
          (congrArg (fun f : CommRingCat.of k ⟶ C.obj n => f r) h).symm
    }
  map_id n := by
    apply ConcreteCategory.hom_ext
    intro x
    change C.map (𝟙 n) x = x
    simp
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro x
    change C.map (f ≫ g) x = C.map g (C.map f x)
    simp

end SerrePositivity.Cosimplicial
