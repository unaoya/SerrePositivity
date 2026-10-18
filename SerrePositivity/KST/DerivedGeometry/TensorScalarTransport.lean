module

public import SerrePositivity.KST.DerivedGeometry.CoefficientTensorPresheaf

/-!
# スカラー構造の等式によるテンソル環の移送

概要：同じ切断環上の二つの A 代数構造の等式をテンソル環へ移す。
方針：代数構造を明示的引数とした環を使い、純テンソルの計算を記録する。
規約：H は非可換でもよい。
使われ方：KST D4、Toën Derived Azumaya §3.2 の係数環層の開制限。
-/

@[expose] public section

noncomputable section

set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace SerrePositivity.KST.DerivedGeometry

variable (A : Type u) [CommRing A] (H : Type u) [Ring H] [Algebra A H]

/--
概要：指定した代数構造で作るテンソル環。
方針：スカラー構造を引数に保持する。
規約：環の束は RingCat とする。
使われ方：KST D4、Toën §3.2 の切断環の移送。
-/
def tensorRingObject (S : Type u) [CommRing S] (α : Algebra A S) : RingCat.{u} := by
  letI := α
  exact RingCat.of (H ⊗[A] S)

/--
概要：指定したスカラー構造のテンソル環の純テンソル。
方針：同じ指定代数構造を使って構成する。
規約：異なる作用を型推論で混在させない。
使われ方：KST D4、Toën §3.2 の移送の計算。
-/
def tensorRingPure (S : Type u) [CommRing S] (α : Algebra A S) (h : H) (s : S) :
    tensorRingObject A H S α := by
  letI := α
  exact h ⊗ₜ[A] s

/--
概要：代数構造の等式による移送は純テンソルを保つ。
方針：等式の帰納で同一の代数構造へ帰着する。
規約：環の圏の eqToHom の値を計算する。
使われ方：KST D4、Toën §3.2 の前層射の自然性。
-/
lemma tensorRingPure_cast (S : Type u) [CommRing S] {α β : Algebra A S}
    (e : α = β) (h : H) (s : S) :
    (eqToHom (congrArg (tensorRingObject A H S) e)) (tensorRingPure A H S α h s) =
      tensorRingPure A H S β h s := by
  cases e
  rfl

/--
概要：指定したテンソル環からの環射は純テンソル上の値で決まる。
方針：テンソルの加法による帰納を使う。
規約：値域は任意の非可換環でもよい。
使われ方：KST D4、Toën §3.2 の環前層比較の自然性。
-/
lemma tensorRingObject_hom_ext (S : Type u) [CommRing S] (α : Algebra A S)
    {N : RingCat.{u}} {f g : tensorRingObject A H S α ⟶ N}
    (hfg : ∀ h s, f (tensorRingPure A H S α h s) = g (tensorRingPure A H S α h s)) :
    f = g := by
  let := α
  apply RingCat.hom_ext
  apply RingHom.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul h s => exact hfg h s
  | add x y hx hy => simp only [map_add, hx, hy]

/--
概要：係数テンソル前層の制限は指定した純テンソルの第二因子を制限する。
方針：テンソル環の制限写像の定義を計算する。
規約：任意のスキームと任意の基礎環写像に対する式。
使われ方：KST D4、Toën §3.2 の開制限の比較射。
-/
lemma coefficientTensorPresheaf_map_ringPure {X : Scheme.{u}} (a : A →+* Γ(X, ⊤))
    {U V : X.Opens} (i : U ⟶ V) (h : H) (s : Γ(X, V)) :
    (coefficientTensorPresheaf H a).map i.op
      (tensorRingPure A H Γ(X, V) (sectionAlgebra a V) h s) =
    tensorRingPure A H Γ(X, U) (sectionAlgebra a U) h (X.presheaf.map i.op s) := rfl

end SerrePositivity.KST.DerivedGeometry
