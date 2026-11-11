module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PointwiseTensorExt
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.PointwiseBaseChange
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleComplete.Basic
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionReflection

/-!
# 完備係数拡大から完備な標的への延長

## 概要
半線形な代数射を、各項の完備係数拡大から完備な標的への線形射に延長する。

## 方針
通常の係数拡大の普遍性と H⁰ 完備化の単位を使う。完備な加群では単位は同型。

## 規約
標的の p 完備性を明記し、平坦性は仮定しない。

## 使われ方
BS 著者版 Theorem 6.4、二つの大きい枠の半線形比較を完備係数拡大後に読む。
-/

public noncomputable section
open CategoryTheory
open scoped TensorProduct ChangeOfRings
universe u
namespace SerrePositivity.DerivedCompletion
set_option backward.isDefEq.respectTransparency false
attribute [local instance] HasDerivedCategory.standard

/-- 完備な加群では H⁰ 主完備化への単位が同型になる。 -/
theorem moduleCompletionH0Unit_isIso_of_complete (R : Type u) [CommRing R] (a : R)
    (M : ModuleCat.{u} R) (hc : IsModuleComplete R a M) :
    IsIso ((moduleCompletionH0Unit R a).app M) := by
  let : IsIso ((derivedComplexCompletionUnit R a).app ((moduleObjectFunctor R).obj M)) :=
    derivedComplexCompletionUnit_isIso_of_isComplete R a _ hc
  dsimp only [moduleCompletionH0Unit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app]
  infer_instance

variable (p : ℕ) (k l A B : Type u) [CommRing k] [CommRing l] [CommRing A] [CommRing B]
variable [Algebra k l] [Algebra k A] [Algebra l B] [Algebra k B] [IsScalarTower k l B]
variable (hc : IsModuleComplete l (p : l) (ModuleCat.of l B)) (f : A →ₐ[k] B)

private def ordinaryExtension :
    (ModuleCat.extendScalars (algebraMap k l)).obj (ModuleCat.of k A) ⟶ ModuleCat.of l B :=
  (algebraScalarExtensionModuleIso k l (ModuleCat.of k A)).hom ≫
    ModuleCat.ofHom (AlgHom.liftEquiv k l A B f).toLinearMap

private theorem ordinaryExtension_tmul (b : l) (x : A) :
    ordinaryExtension k l A B f (b ⊗ₜ[k,algebraMap k l] x) = b • f x := by
  change (AlgHom.liftEquiv k l A B f)
    ((algebraScalarExtensionModuleIso k l (ModuleCat.of k A)).hom
      (b ⊗ₜ[k,algebraMap k l] x)) = _
  rw [algebraScalarExtensionModuleIso_tmul, AlgHom.liftEquiv_tmul]

/-- 半線形な代数射を各項の完備係数拡大から完備な標的への線形射へ延長する。 -/
def pointwiseCompletedAlgMap :
    (pCompletedScalarExtensionFunctor p (algebraMap k l)).obj (ModuleCat.of k A) ⟶
      ModuleCat.of l B := by
  let := moduleCompletionH0Unit_isIso_of_complete l (p : l) (ModuleCat.of l B) hc
  exact (moduleCompletionH0Functor l (p : l)).map (ordinaryExtension k l A B f) ≫
    inv ((moduleCompletionH0Unit l (p : l)).app (ModuleCat.of l B))

/-- 延長は純テンソルの完備化単位上で元の半線形射を与える。 -/
theorem pointwiseCompletedAlgMap_unit (b : l) (x : A) :
    pointwiseCompletedAlgMap p k l A B hc f
      (((moduleCompletionH0Unit l (p : l)).app
        ((ModuleCat.extendScalars (algebraMap k l)).obj (ModuleCat.of k A)))
          (b ⊗ₜ[k,algebraMap k l] x)) = b • f x := by
  let := moduleCompletionH0Unit_isIso_of_complete l (p : l) (ModuleCat.of l B) hc
  let u := (moduleCompletionH0Unit l (p : l)).app (ModuleCat.of l B)
  let g := ordinaryExtension k l A B f
  have hn := ConcreteCategory.congr_hom ((moduleCompletionH0Unit l (p : l)).naturality g)
    (b ⊗ₜ[k,algebraMap k l] x)
  change u (g (b ⊗ₜ[k,algebraMap k l] x)) =
    (moduleCompletionH0Functor l (p : l)).map g
      (((moduleCompletionH0Unit l (p : l)).app
        ((ModuleCat.extendScalars (algebraMap k l)).obj (ModuleCat.of k A)))
          (b ⊗ₜ[k,algebraMap k l] x)) at hn
  change inv u ((moduleCompletionH0Functor l (p : l)).map g _) = _
  rw [← hn]
  exact (ConcreteCategory.congr_hom (IsIso.hom_inv_id u) _).trans
    (ordinaryExtension_tmul k l A B f b x)

variable {A' B' : Type u} [CommRing A'] [CommRing B'] [Algebra k A']
variable [Algebra l B'] [Algebra k B'] [IsScalarTower k l B']

/-- 元の代数射の正方形が可換なら、完備係数拡大後の線形延長も厳密に可換。 -/
theorem pointwiseCompletedAlgMap_naturality (α : A →ₐ[k] A') (β : B →ₐ[l] B')
    (hc' : IsModuleComplete l (p : l) (ModuleCat.of l B')) (g : A' →ₐ[k] B')
    (h : (β.restrictScalars k).comp f = g.comp α) :
    (pCompletedScalarExtensionFunctor p (algebraMap k l)).map (ModuleCat.ofHom α.toLinearMap) ≫
        pointwiseCompletedAlgMap p k l A' B' hc' g =
      pointwiseCompletedAlgMap p k l A B hc f ≫ ModuleCat.ofHom β.toLinearMap := by
  apply pCompletedScalarExtension_hom_ext p k l A (ModuleCat.of l B') hc'
  intro b x
  change pointwiseCompletedAlgMap p k l A' B' hc' g
      ((pCompletedScalarExtensionFunctor p (algebraMap k l)).map (ModuleCat.ofHom α.toLinearMap) _) =
    β (pointwiseCompletedAlgMap p k l A B hc f _)
  rw [pCompletedScalarExtension_map_unit, pointwiseCompletedAlgMap_unit,
    pointwiseCompletedAlgMap_unit, map_smul]
  exact congrArg (b • ·) (AlgHom.congr_fun h x).symm

end SerrePositivity.DerivedCompletion
