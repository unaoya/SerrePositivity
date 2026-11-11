module

public import SerrePositivity.HomologicalAlgebra.Cosimplicial.Algebra
public import SerrePositivity.HomologicalAlgebra.Cosimplicial.MapComplex
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PointwiseExtension
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.Algebra

/-!
# 完備係数拡大後の半線形な余単体射

## 概要
係数を変える余単体的な環射を、各項の完備係数拡大後の線形な余単体射に延長する。

## 方針
各項の代数射を完備な標的へ延長し、元の正方形と延長の自然性から余面自然性を得る。

## 規約
標的の各項の p 完備性を明記する。完全性・平坦性は仮定しない。

## 使われ方
BS 著者版 Theorem 6.4、大きい枠の二比較を古典的な複体に移す。
-/

public noncomputable section
open CategoryTheory AlgebraicTopology
open scoped TensorProduct ChangeOfRings
open SerrePositivity.DerivedCompletion
universe u
namespace SerrePositivity.Cosimplicial
set_option backward.isDefEq.respectTransparency false
variable (p : ℕ) (k l : Type u) [CommRing k] [CommRing l] [Algebra k l]
variable (X Y : CosimplicialObject CommRingCat.{u})
variable (ιX : (Functor.const SimplexCategory).obj (CommRingCat.of k) ⟶ X)
variable (ιY : (Functor.const SimplexCategory).obj (CommRingCat.of l) ⟶ Y)
variable (f : X ⟶ Y)
variable (hι : ∀ n, (f.app n).hom.comp (ιX.app n).hom =
  (ιY.app n).hom.comp (algebraMap k l))
variable (hc : ∀ n, IsModuleComplete l (p : l) ((toModules l Y ιY).obj n))

private def coefficientAlgHom (n : SimplexCategory) :
    letI : Algebra k (X.obj n) := (ιX.app n).hom.toAlgebra
    letI : Algebra k (Y.obj n) := ((ιY.app n).hom.comp (algebraMap k l)).toAlgebra
    X.obj n →ₐ[k] Y.obj n := by
  let : Algebra k (X.obj n) := (ιX.app n).hom.toAlgebra
  let : Algebra k (Y.obj n) := ((ιY.app n).hom.comp (algebraMap k l)).toAlgebra
  exact ⟨(f.app n).hom, fun a => RingHom.congr_fun (hι n) a⟩

private theorem scalarTower (n : SimplexCategory) :
    letI : Algebra l (Y.obj n) := (ιY.app n).hom.toAlgebra
    letI : Algebra k (Y.obj n) := ((ιY.app n).hom.comp (algebraMap k l)).toAlgebra
    IsScalarTower k l (Y.obj n) := by
  let : Algebra l (Y.obj n) := (ιY.app n).hom.toAlgebra
  let : Algebra k (Y.obj n) := ((ιY.app n).hom.comp (algebraMap k l)).toAlgebra
  exact IsScalarTower.of_algebraMap_eq (fun _ => rfl)

private def structureAlgHom (R : Type u) [CommRing R]
    (Z : CosimplicialObject CommRingCat.{u})
    (ιZ : (Functor.const SimplexCategory).obj (CommRingCat.of R) ⟶ Z)
    {m n : SimplexCategory} (θ : m ⟶ n) :
    letI : Algebra R (Z.obj m) := (ιZ.app m).hom.toAlgebra
    letI : Algebra R (Z.obj n) := (ιZ.app n).hom.toAlgebra
    Z.obj m →ₐ[R] Z.obj n := by
  let : Algebra R (Z.obj m) := (ιZ.app m).hom.toAlgebra
  let : Algebra R (Z.obj n) := (ιZ.app n).hom.toAlgebra
  refine ⟨(Z.map θ).hom, ?_⟩
  intro a
  have h := ιZ.naturality θ
  change 𝟙 _ ≫ ιZ.app n = ιZ.app m ≫ Z.map θ at h
  rw [Category.id_comp] at h
  exact (ConcreteCategory.congr_hom h a).symm

private def component (n : SimplexCategory) :
    (pCompletedScalarExtensionFunctor p (algebraMap k l)).obj ((toModules k X ιX).obj n) ⟶
      (toModules l Y ιY).obj n := by
  let : Algebra k (X.obj n) := (ιX.app n).hom.toAlgebra
  let : Algebra l (Y.obj n) := (ιY.app n).hom.toAlgebra
  let : Algebra k (Y.obj n) := ((ιY.app n).hom.comp (algebraMap k l)).toAlgebra
  let := scalarTower k l Y ιY n
  exact pointwiseCompletedAlgMap p k l (X.obj n) (Y.obj n) (hc n)
    (coefficientAlgHom k l X Y ιX ιY f hι n)

/-- 半線形な余単体射の、各項の完備係数拡大後の標準線形延長。 -/
def completedCoefficientMap :
    toModules k X ιX ⋙ pCompletedScalarExtensionFunctor p (algebraMap k l) ⟶
      toModules l Y ιY where
  app n := component p k l X Y ιX ιY f hι hc n
  naturality {m n} θ := by
    let : Algebra k (X.obj m) := (ιX.app m).hom.toAlgebra
    let : Algebra k (X.obj n) := (ιX.app n).hom.toAlgebra
    let : Algebra l (Y.obj m) := (ιY.app m).hom.toAlgebra
    let : Algebra l (Y.obj n) := (ιY.app n).hom.toAlgebra
    let : Algebra k (Y.obj m) := ((ιY.app m).hom.comp (algebraMap k l)).toAlgebra
    let : Algebra k (Y.obj n) := ((ιY.app n).hom.comp (algebraMap k l)).toAlgebra
    let := scalarTower k l Y ιY m
    let := scalarTower k l Y ιY n
    exact pointwiseCompletedAlgMap_naturality p k l (X.obj m) (Y.obj m)
      (A' := X.obj n) (B' := Y.obj n) (hc m)
      (coefficientAlgHom k l X Y ιX ιY f hι m)
      (structureAlgHom k X ιX (m := m) (n := n) θ)
      (structureAlgHom l Y ιY (m := m) (n := n) θ) (hc n)
      (coefficientAlgHom k l X Y ιX ιY f hι n) (by
        apply AlgHom.ext
        intro x
        exact (ConcreteCategory.congr_hom (f.naturality θ) x).symm)

/-- 元の半線形な環射を、二つの台加群の間の関数として読む。 -/
def coefficientTermFunction (n : SimplexCategory) :
    (toModules k X ιX).obj n → (toModules l Y ιY).obj n :=
  f.app n

/-- 標準の余単体的延長は、純テンソルの完備化単位上で元の射を与える。 -/
theorem completedCoefficientMap_unit (n : SimplexCategory) (b : l)
    (x : (toModules k X ιX).obj n) :
    (completedCoefficientMap p k l X Y ιX ιY f hι hc).app n
      (((moduleCompletionH0Unit l (p : l)).app
        ((ModuleCat.extendScalars (algebraMap k l)).obj ((toModules k X ιX).obj n)))
          (b ⊗ₜ[k,algebraMap k l] x)) = b • coefficientTermFunction k l X Y ιX ιY f n x := by
  let : Algebra k (X.obj n) := (ιX.app n).hom.toAlgebra
  let : Algebra l (Y.obj n) := (ιY.app n).hom.toAlgebra
  let : Algebra k (Y.obj n) := ((ιY.app n).hom.comp (algebraMap k l)).toAlgebra
  let := scalarTower k l Y ιY n
  exact pointwiseCompletedAlgMap_unit p k l (X.obj n) (Y.obj n) (hc n)
    (coefficientAlgHom k l X Y ιX ιY f hι n) b x

/-- 半線形な環射を、各項の完備係数変更後の交代余面複体の射に延長する。 -/
def completedCoefficientCochainMap :
    ((pCompletedScalarExtensionFunctor p (algebraMap k l)).mapHomologicalComplex _).obj
      ((alternatingCofaceMapComplex (ModuleCat.{u} k)).obj (toModules k X ιX)) ⟶
    (alternatingCofaceMapComplex (ModuleCat.{u} l)).obj (toModules l Y ιY) :=
  ((alternatingCofaceMapComplexCompMapHomologicalComplexIso
      (pCompletedScalarExtensionFunctor p (algebraMap k l))).app (toModules k X ιX)).hom ≫
    (alternatingCofaceMapComplex (ModuleCat.{u} l)).map
      (completedCoefficientMap p k l X Y ιX ιY f hι hc)

end SerrePositivity.Cosimplicial
