module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PointwiseTensor
import all Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.PointwiseTensor
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.PointwiseBaseChange
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionFunctor

/-!
# 各項の完備係数拡大からの線形写像の一意性

## 概要
完備な加群への射は、係数拡大と完備化の単位の上で決まる。

## 方針
通常テンソルの主完備化との比較を通し、完備化の普遍性と純テンソルを使う。

## 規約
環の平坦性や正則性は仮定しない。標的には p 完備性を明記する。

## 使われ方
BS 著者版 Theorem 6.4、各項の同型を余単体の構造射に合わせる。
-/

public noncomputable section
open CategoryTheory
open scoped TensorProduct ChangeOfRings
universe u
namespace SerrePositivity.DerivedCompletion
set_option backward.isDefEq.respectTransparency false
variable (p : ℕ) (k l A : Type u) [CommRing k] [CommRing l] [CommRing A]
variable [Algebra k l] [Algebra k A]
local notation "F" => pCompletedScalarExtensionFunctor p (algebraMap k l)
local notation "E" => Functor.obj (ModuleCat.extendScalars (algebraMap k l)) (ModuleCat.of k A)
local notation "U" => NatTrans.app (moduleCompletionH0Unit l (p : l)) E

/-- 通常テンソルの単位の像を、各項の完備係数拡大へ戻す式。 -/
theorem pCompletedScalarExtensionTensorIso_inv_unit (b : l) (x : A) :
    (pCompletedScalarExtensionTensorIso p k l A).inv
      (principalCompletionRingCatUnit p (CommRingCat.of (l ⊗[k] A)) (b ⊗ₜ[k] x)) =
        U (b ⊗ₜ[k,algebraMap k l] x) := by
  let e := pCompletedScalarExtensionTensorIso p k l A
  have h := pCompletedScalarExtensionTensorIso_unit p k l A b x
  have he := ConcreteCategory.congr_hom e.hom_inv_id (U (b ⊗ₜ[k,algebraMap k l] x))
  change e.inv (e.hom (U (b ⊗ₜ[k,algebraMap k l] x))) = U (b ⊗ₜ[k,algebraMap k l] x) at he
  rw [h] at he
  exact he

/-- 完備な標的への二射は、純テンソルの単位上で一致すれば等しい。 -/
theorem pCompletedScalarExtension_hom_ext (M : ModuleCat.{u} l)
    (hc : IsModuleComplete l (p : l) M) (g h : (F).obj (ModuleCat.of k A) ⟶ M)
    (hu : ∀ (b : l) (x : A), g (U (b ⊗ₜ[k,algebraMap k l] x)) =
      h (U (b ⊗ₜ[k,algebraMap k l] x))) : g = h := by
  let e := pCompletedScalarExtensionTensorIso p k l A
  apply (cancel_epi e.inv).mp
  apply ModuleCat.hom_ext
  apply principalCompletionLinearMap_ext l p hc
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul b x =>
    change g (e.inv (principalCompletionRingCatUnit p (CommRingCat.of (l ⊗[k] A))
      (b ⊗ₜ[k] x))) = h (e.inv (principalCompletionRingCatUnit p (CommRingCat.of (l ⊗[k] A))
      (b ⊗ₜ[k] x)))
    rw [pCompletedScalarExtensionTensorIso_inv_unit]
    exact hu b x
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

variable {A} {B : Type u} [CommRing B] [Algebra k B]

/-- 各項の完備係数拡大の射は、純テンソルの完備化単位と可換。 -/
theorem pCompletedScalarExtension_map_unit (f : A →ₐ[k] B) (b : l) (x : A) :
    (pCompletedScalarExtensionFunctor p (algebraMap k l)).map (ModuleCat.ofHom f.toLinearMap)
        (((moduleCompletionH0Unit l (p : l)).app
          ((ModuleCat.extendScalars (algebraMap k l)).obj (ModuleCat.of k A)))
            (b ⊗ₜ[k,algebraMap k l] x)) =
      ((moduleCompletionH0Unit l (p : l)).app
        ((ModuleCat.extendScalars (algebraMap k l)).obj (ModuleCat.of k B)))
          (b ⊗ₜ[k,algebraMap k l] f x) := by
  let g := (ModuleCat.extendScalars (algebraMap k l)).map (ModuleCat.ofHom f.toLinearMap)
  have hn := ConcreteCategory.congr_hom ((moduleCompletionH0Unit l (p : l)).naturality g)
    (b ⊗ₜ[k,algebraMap k l] x)
  change ((moduleCompletionH0Unit l (p : l)).app
      ((ModuleCat.extendScalars (algebraMap k l)).obj (ModuleCat.of k B)))
        (g (b ⊗ₜ[k,algebraMap k l] x)) =
    (moduleCompletionH0Functor l (p : l)).map g
      (((moduleCompletionH0Unit l (p : l)).app
        ((ModuleCat.extendScalars (algebraMap k l)).obj (ModuleCat.of k A)))
          (b ⊗ₜ[k,algebraMap k l] x)) at hn
  change (moduleCompletionH0Functor l (p : l)).map g _ = _
  rw [← hn]
  exact congrArg (((moduleCompletionH0Unit l (p : l)).app
    ((ModuleCat.extendScalars (algebraMap k l)).obj (ModuleCat.of k B))))
      (ModuleCat.ExtendScalars.map_tmul (algebraMap k l) (ModuleCat.ofHom f.toLinearMap) b x)

/-- 任意の加群射について、各項の完備係数拡大の単位は自然。 -/
theorem pCompletedScalarExtension_map_unit_linear {M N : ModuleCat.{u} k}
    (f : M ⟶ N) (b : l) (x : M) :
    (pCompletedScalarExtensionFunctor p (algebraMap k l)).map f
      (((moduleCompletionH0Unit l (p : l)).app
        ((ModuleCat.extendScalars (algebraMap k l)).obj M)) (b ⊗ₜ[k,algebraMap k l] x)) =
    ((moduleCompletionH0Unit l (p : l)).app
      ((ModuleCat.extendScalars (algebraMap k l)).obj N)) (b ⊗ₜ[k,algebraMap k l] f x) := by
  let g := (ModuleCat.extendScalars (algebraMap k l)).map f
  have hn := ConcreteCategory.congr_hom ((moduleCompletionH0Unit l (p : l)).naturality g)
    (b ⊗ₜ[k,algebraMap k l] x)
  change ((moduleCompletionH0Unit l (p : l)).app
      ((ModuleCat.extendScalars (algebraMap k l)).obj N)) (g (b ⊗ₜ[k,algebraMap k l] x)) =
    (moduleCompletionH0Functor l (p : l)).map g
      (((moduleCompletionH0Unit l (p : l)).app
        ((ModuleCat.extendScalars (algebraMap k l)).obj M)) (b ⊗ₜ[k,algebraMap k l] x)) at hn
  change (moduleCompletionH0Functor l (p : l)).map g _ = _
  rw [← hn]
  exact congrArg (((moduleCompletionH0Unit l (p : l)).app
    ((ModuleCat.extendScalars (algebraMap k l)).obj N)))
      (ModuleCat.ExtendScalars.map_tmul (algebraMap k l) f b x)

end SerrePositivity.DerivedCompletion
