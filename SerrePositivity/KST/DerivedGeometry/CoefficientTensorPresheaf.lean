module

public import SerrePositivity.KST.DerivedGeometry.BaseSections
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.AlgebraicGeometry.Modules.Presheaf

/-!
# 非可換係数のテンソル前層

概要：開 U 上で H ⊗_A O_X(U) を取る環の前層を構成する。
方針：構造層の制限を A 代数準同型にしてテンソルする。
規約：H は単位的結合 A 代数。H の可換性・平坦性は要求しない。
使われ方：KST D4、Toën Derived Azumaya §3.2 の係数環層とアフィン模型。
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped TensorProduct

namespace SerrePositivity.KST.DerivedGeometry

variable {A : Type u} [CommRing A] (H : Type u) [Ring H] [Algebra A H]
  {X : Scheme.{u}} (a : A →+* Γ(X, ⊤))

/--
概要：各開の切断に H をテンソルして作る非可換環の前層。
方針：制限の A 線形性を使い、テンソル積の写像で前層の射を定める。
規約：この段階で任意の開被覆に対する層条件を主張しない。
使われ方：KST D4、Toën §3.2 の H_X の層化前の模型。
-/
def coefficientTensorPresheaf : TopCat.Presheaf RingCat.{u} X := by
  letI (U : X.Opens) : Algebra A Γ(X, U) := sectionAlgebra a U
  exact
    { obj := fun U => RingCat.of (H ⊗[A] Γ(X, U.unop))
      map := fun i => RingCat.ofHom
        (Algebra.TensorProduct.map (AlgHom.id A H) (sectionRestriction a i.unop)).toRingHom
      map_id := fun U => by
        apply RingCat.hom_ext
        apply RingHom.ext
        intro x
        induction x using TensorProduct.inductionOn with
        | tmul h r =>
          change h ⊗ₜ[A] (X.presheaf.map (𝟙 U)).hom r = h ⊗ₜ[A] r
          rw [X.presheaf.map_id]
          rfl
        | add x y hx hy => simp only [map_add, hx, hy]
      map_comp := fun i j => by
        apply RingCat.hom_ext
        apply RingHom.ext
        intro x
        induction x using TensorProduct.inductionOn with
        | tmul h r =>
          change h ⊗ₜ[A] (X.presheaf.map (i ≫ j)).hom r =
            h ⊗ₜ[A] (X.presheaf.map j).hom ((X.presheaf.map i).hom r)
          rw [X.presheaf.map_comp]
          rfl
        | add x y hx hy => simp only [map_add, hx, hy] }

/--
概要：構造層から係数テンソル前層への単位的な環準同型。
方針：各開で r を 1 ⊗ r に送る。
規約：非可換環 H の右因子への包含を使い、積の順序を変えない。
使われ方：KST D4、Toën §3.2 の H_X 上の加群から構造層上の加群への忘却。
-/
def coefficientTensorUnit : X.ringCatSheaf.obj ⟶ coefficientTensorPresheaf H a := by
  letI (U : X.Opens) : Algebra A Γ(X, U) := sectionAlgebra a U
  exact
    { app := fun U => RingCat.ofHom
        (Algebra.TensorProduct.includeRight (A := H) (R := A) (B := Γ(X, U.unop))).toRingHom
      naturality := fun {U V} i => by
        apply RingCat.hom_ext
        apply RingHom.ext
        intro r
        rfl }

end SerrePositivity.KST.DerivedGeometry
