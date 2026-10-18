module

public import SerrePositivity.KST.DerivedGeometry.CoefficientTensorPresheaf

/-!
# テンソル前層の二つの因子の作用

概要：H の定数前層からの写像、構造層の中心的作用、A 上の両立性を証明する。
方針：テンソル積の左右の包含と純テンソルによる帰納を使う。
規約：構造層の可換性を使い、H の可換性は仮定しない。
使われ方：KST D4、Toën Derived Azumaya §3.2 の具体的係数環層の作用。
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
概要：H の定数前層から係数テンソル前層への写像。
方針：各開で h を h ⊗ 1 に送る。
規約：定数前層が層であるとは仮定しない。
使われ方：KST D4、Toën §3.2 の具体的な係数作用。
-/
def coefficientTensorConstant :
    (Functor.const (Opens X)ᵒᵖ).obj (RingCat.of H) ⟶ coefficientTensorPresheaf H a := by
  letI (U : X.Opens) : Algebra A Γ(X, U) := sectionAlgebra a U
  exact
    { app := fun U => RingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := H) (B := Γ(X, U.unop)))
      naturality := fun {U V} i => by
        apply RingCat.hom_ext
        apply RingHom.ext
        intro h
        change H at h
        change h ⊗ₜ[A] (1 : Γ(X, V.unop)) =
          h ⊗ₜ[A] (sectionRestriction a i.unop) 1
        rw [map_one] }

/--
概要：構造層の切断の像は係数テンソル環の全元と可換。
方針：純テンソルの積を計算し、加法について帰納する。
規約：H の元同士の可換性は主張しない。
使われ方：KST D4、Toën §3.2 の構造層上の非可換係数代数。
-/
lemma coefficientTensorUnit_commutes (U : X.Opens) (r : Γ(X, U))
    (x : (coefficientTensorPresheaf H a).obj (.op U)) :
    Commute ((coefficientTensorUnit H a).app (.op U) r) x := by
  let (V : X.Opens) : Algebra A Γ(X, V) := sectionAlgebra a V
  change Commute (1 ⊗ₜ[A] r : H ⊗[A] Γ(X, U)) x
  induction x using TensorProduct.inductionOn with
  | tmul h s =>
    change (1 ⊗ₜ[A] r) * (h ⊗ₜ[A] s) = (h ⊗ₜ[A] s) * (1 ⊗ₜ[A] r)
    simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, mul_comm]
  | add x y hx hy => exact hx.add_right hy

/--
概要：H と構造層からの二つの包含は A の作用について一致する。
方針：テンソル積の基礎環の釣合い関係を使う。
規約：作用の一致を実際の環準同型の等式で表す。
使われ方：KST D4、Toën §3.2 の H_X の A 線形性。
-/
lemma coefficientTensorConstant_comp_algebraMap (U : X.Opens) :
    ((coefficientTensorConstant H a).app (.op U)).hom.comp (algebraMap A H) =
      ((coefficientTensorUnit H a).app (.op U)).hom.comp (sectionBaseMap a U) := by
  let (V : X.Opens) : Algebra A Γ(X, V) := sectionAlgebra a V
  exact Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
    (R := A) (A := H) (B := Γ(X, U))

end SerrePositivity.KST.DerivedGeometry
