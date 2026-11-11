module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PointwiseAlgebra
public import SerrePositivity.HomologicalAlgebra.AlgebraScalarExtensionModule
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.PointwiseBaseChange
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.PointwiseAlgebra

/-!
# 各項の完備係数拡大と通常テンソル環

## 概要
自然数 p で指定した各項の完備係数拡大を、通常テンソル環の主完備化に同定する。

## 方針
p の像を正規化し、既存の係数拡大の加群比較と主完備環の H⁰ 比較を合成する。

## 規約
通常テンソルの元と主完備化の単位を保つ。導来底変換との同定には別の離散性を使う。

## 使われ方
BS 著者版 Theorem 6.4 の各項の完備テンソルと有限枠の実際の射の照合。
-/

public noncomputable section

open CategoryTheory
open scoped TensorProduct ChangeOfRings

universe u

namespace SerrePositivity.DerivedCompletion

set_option backward.isDefEq.respectTransparency false

variable (p : ℕ) {k l : Type u} [CommRing k] [CommRing l] (φ : k →+* l)

/-- 自然数 p の像で正規化した各項の完備係数拡大。 -/
@[expose] def pCompletedScalarExtensionFunctor : ModuleCat.{u} k ⥤ ModuleCat.{u} l :=
  ModuleCat.extendScalars φ ⋙ moduleCompletionH0Functor l (p : l)

instance : (pCompletedScalarExtensionFunctor p φ).Additive := by
  dsimp [pCompletedScalarExtensionFunctor]
  infer_instance

/-- 係数射で写した p と終域の p の像による二つの表示を合わせる。 -/
def pCompletedScalarExtensionFunctorIso :
    pointwiseCompletedBaseChangeFunctor (p : k) φ ≅ pCompletedScalarExtensionFunctor p φ :=
  eqToIso (by
    unfold pointwiseCompletedBaseChangeFunctor pCompletedScalarExtensionFunctor
    rw [map_natCast])

variable (k l) [Algebra k l] (A : Type u) [CommRing A] [Algebra k A]

/-- 各項の完備係数拡大を、通常テンソル環の主完備化として読む標準の線形同型。 -/
def pCompletedScalarExtensionTensorIso :
    (pCompletedScalarExtensionFunctor p (algebraMap k l)).obj (ModuleCat.of k A) ≅
      ModuleCat.of l (CompletedRing p (l ⊗[k] A)) :=
  (moduleCompletionH0Functor l (p : l)).mapIso
      (algebraScalarExtensionModuleIso k l (ModuleCat.of k A)) ≪≫
    moduleCompletionH0RingIso l p (l ⊗[k] A)

/-- 通常テンソルの標準の元は、比較の下で主完備化の同じ元に写る。 -/
theorem pCompletedScalarExtensionTensorIso_unit (b : l) (x : A) :
    (pCompletedScalarExtensionTensorIso p k l A).hom
        (((moduleCompletionH0Unit l (p : l)).app
          ((ModuleCat.extendScalars (algebraMap k l)).obj (ModuleCat.of k A)))
            (b ⊗ₜ[k,algebraMap k l] x)) =
      principalCompletionRingCatUnit p (CommRingCat.of (l ⊗[k] A)) (b ⊗ₜ[k] x) := by
  let e := algebraScalarExtensionModuleIso k l (ModuleCat.of k A)
  have hn := ConcreteCategory.congr_hom
    ((moduleCompletionH0Unit l (p : l)).naturality e.hom) (b ⊗ₜ[k,algebraMap k l] x)
  change ((moduleCompletionH0Unit l (p : l)).app (ModuleCat.of l (l ⊗[k] A)))
      (e.hom (b ⊗ₜ[k,algebraMap k l] x)) =
    (moduleCompletionH0Functor l (p : l)).map e.hom
      (((moduleCompletionH0Unit l (p : l)).app
        ((ModuleCat.extendScalars (algebraMap k l)).obj (ModuleCat.of k A)))
          (b ⊗ₜ[k,algebraMap k l] x)) at hn
  change (moduleCompletionH0RingIso l p (l ⊗[k] A)).hom
    ((moduleCompletionH0Functor l (p : l)).map e.hom _) = _
  rw [← hn, algebraScalarExtensionModuleIso_tmul, moduleCompletionH0RingIso_unit]

variable {A} {B : Type u} [CommRing B] [Algebra k B]

/-- 通常テンソルの主完備化との比較は、元の代数射について厳密に自然。 -/
theorem pCompletedScalarExtensionTensorIso_naturality (f : A →ₐ[k] B) :
    (pCompletedScalarExtensionFunctor p (algebraMap k l)).map (ModuleCat.ofHom f.toLinearMap) ≫
        (pCompletedScalarExtensionTensorIso p k l B).hom =
      (pCompletedScalarExtensionTensorIso p k l A).hom ≫
        ModuleCat.ofHom (principalCompletionLinearMap l p
          (Algebra.TensorProduct.map (AlgHom.id l l) f).toLinearMap) := by
  have he : (ModuleCat.extendScalars (algebraMap k l)).map (ModuleCat.ofHom f.toLinearMap) ≫
        (algebraScalarExtensionModuleIso k l (ModuleCat.of k B)).hom =
      (algebraScalarExtensionModuleIso k l (ModuleCat.of k A)).hom ≫
        ModuleCat.ofHom (Algebra.TensorProduct.map (AlgHom.id l l) f).toLinearMap := by
    apply ModuleCat.hom_ext
    ext z
    exact algebraScalarExtensionModuleIso_algMap_apply k l f z
  dsimp only [pCompletedScalarExtensionFunctor, pCompletedScalarExtensionTensorIso]
  simp only [Functor.comp_map, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [← Category.assoc, ← Functor.map_comp, he, Functor.map_comp, Category.assoc,
    moduleCompletionH0RingIso_naturality]

end SerrePositivity.DerivedCompletion
