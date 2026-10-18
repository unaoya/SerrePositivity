module

public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.CategoryTheory.Sites.PreservesSheafification

/-!
# 基礎集合を保つ忘却関手と層化

概要：基礎集合を保つ関手が層化の同値を保存することを証明する。
方針：層化の同値を局所全単射性で判定し、同じ基礎集合の射へ忘れる。
規約：局所全単射性による判定は両方の値域で要求する。
使われ方：KST D4、Toën Derived Azumaya §3.2 の係数環と加群の層化比較。
-/

@[expose] public section

universe u v v' w w'

open CategoryTheory TopologicalSpace

namespace SerrePositivity.KST.DerivedGeometry

/--
概要：基礎集合への忘却と可換な関手は、局所全単射による層化の同値を保存する。
方針：局所単射・局所全射を基礎集合の前層で確認する。
規約：関手の完全性や圏の生成定理を仮定しない。
使われ方：KST D4、Toën §3.2 の環から加法群への層化の移送。
-/
lemma preservesSheafification_of_forget {X : TopCat.{u}}
    {C : Type v} [Category.{w} C] {D : Type v'} [Category.{w'} D]
    {FC : C → C → Type*} {CC : C → Type u}
    [∀ P Q, FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u} C FC]
    {FD : D → D → Type*} {CD : D → Type u}
    [∀ P Q, FunLike (FD P Q) (CD P) (CD Q)] [ConcreteCategory.{u} D FD]
    (F : C ⥤ D) (hF : F ⋙ forget D = forget C)
    [(Opens.grothendieckTopology X).WEqualsLocallyBijective C]
    [(Opens.grothendieckTopology X).WEqualsLocallyBijective D] :
    (Opens.grothendieckTopology X).PreservesSheafification F where
  le {P Q} f hf := by
    have : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X) f := hf.isLocallyInjective
    have : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) f := hf.isLocallySurjective
    apply ((Opens.grothendieckTopology X).W_iff_isLocallyBijective (Functor.whiskerRight f F)).mpr
    constructor
    · apply (Presheaf.isLocallyInjective_forget_iff _ _).mp
      change Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
        (Functor.whiskerRight f (F ⋙ forget D))
      rw [hF]
      infer_instance
    · apply (Presheaf.isLocallySurjective_iff_whisker_forget _ _).mpr
      change Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
        (Functor.whiskerRight f (F ⋙ forget D))
      rw [hF]
      infer_instance

end SerrePositivity.KST.DerivedGeometry
