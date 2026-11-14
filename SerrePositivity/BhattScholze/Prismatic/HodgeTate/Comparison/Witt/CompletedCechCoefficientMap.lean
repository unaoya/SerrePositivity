module

public import SerrePositivity.HomologicalAlgebra.Cosimplicial.Algebra.FrameHelpers
public import SerrePositivity.HomologicalAlgebra.Cosimplicial.CompletedCoefficientMap
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.CompletedCoefficientMap
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.PointwiseBaseChange
import all Mathlib.Algebra.Category.ModuleCat.Basic
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.Algebra.FrameHelpers
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.Algebra
import all Mathlib.Algebra.Category.CommAlgCat.Basic

/-!
# 基底の下の Čech 模型の完備係数射

## 概要
基底を変える厳密な余単体的代数射を、完備係数拡大後の台加群の射に移す。

## 方針
既存の枠の鎖ホモトピーが使う台加群関手を、係数の構造射から作る台加群と合わせる。
半線形余単体射の共通の完備延長を、この同型の間で読む。

## 規約
標的の各項の p 完備性を明記する。∞ 圏の構造には依存しない。

## 使われ方
BS 著者版 Theorem 6.4、大きい枠と有限枠の比較。
-/

public noncomputable section
open CategoryTheory AlgebraicTopology
open scoped TensorProduct ChangeOfRings
open SerrePositivity.DerivedCompletion
universe u
namespace SerrePositivity.BhattScholze.Prismatic
set_option backward.isDefEq.respectTransparency false

/-- 基底の下の余単体的環から、係数の構造自然変換を取り出す。 -/
def underCechBase (k : Type u) [CommRing k]
    (D : SerrePositivity.Cosimplicial.CosimplicialAlgebra k) :
    (Functor.const SimplexCategory).obj (CommRingCat.of k) ⟶ D ⋙ Under.forget (CommRingCat.of k) where
  app n := (D.obj n).hom
  naturality _ _ θ := (Category.id_comp _).trans (Under.w (D.map θ)).symm

/-- 枠のホモトピーの台加群と、構造射から作った台加群の標準比較。 -/
def underCechModuleIso (k : Type u) [CommRing k]
    (D : SerrePositivity.Cosimplicial.CosimplicialAlgebra k) :
    D ⋙ PDCechNerve.algebraModule k ≅
      SerrePositivity.Cosimplicial.toModules k (D ⋙ Under.forget (CommRingCat.of k))
        (underCechBase k D) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun {_ _} θ => by
    apply ModuleCat.hom_ext
    ext x
    rfl)

variable (p : ℕ) (k l : Type u) [CommRing k] [CommRing l] [Algebra k l]
variable (D : SerrePositivity.Cosimplicial.CosimplicialAlgebra k)
variable (E : SerrePositivity.Cosimplicial.CosimplicialAlgebra l)
variable (f : D ⟶ E ⋙ Under.map (CommRingCat.ofHom (algebraMap k l)))
variable (hc : ∀ n, IsModuleComplete l (p : l) ((E ⋙ PDCechNerve.algebraModule l).obj n))

private def coefficientRings :
    D ⋙ Under.forget (CommRingCat.of k) ⟶ E ⋙ Under.forget (CommRingCat.of l) where
  app n := (f.app n).right
  naturality {_ _} θ := congrArg (fun t => Under.Hom.right t) (f.naturality θ)

private theorem coefficientBase (n : SimplexCategory) :
    ((coefficientRings k l D E f).app n).hom.comp ((underCechBase k D).app n).hom =
      ((underCechBase l E).app n).hom.comp (algebraMap k l) := by
  apply RingHom.ext
  intro a
  exact ConcreteCategory.congr_hom (Under.w (f.app n)) a

include hc in
private theorem targetComplete (n : SimplexCategory) :
    IsModuleComplete l (p : l)
      ((SerrePositivity.Cosimplicial.toModules l (E ⋙ Under.forget (CommRingCat.of l))
        (underCechBase l E)).obj n) :=
  isModuleComplete_of_linearEquiv l (p : l) _ _
    ((underCechModuleIso l E).app n).toLinearEquiv (hc n)

/-- 完備係数拡大後の線形余単体射を、既存の枠の台加群関手で読む。 -/
def completedUnderCechCoefficientMap :
    D ⋙ PDCechNerve.algebraModule k ⋙ pCompletedScalarExtensionFunctor p (algebraMap k l) ⟶
      E ⋙ PDCechNerve.algebraModule l :=
  Functor.whiskerRight (underCechModuleIso k D).hom
      (pCompletedScalarExtensionFunctor p (algebraMap k l)) ≫
    SerrePositivity.Cosimplicial.completedCoefficientMap p k l
      (D ⋙ Under.forget (CommRingCat.of k)) (E ⋙ Under.forget (CommRingCat.of l))
      (underCechBase k D) (underCechBase l E) (coefficientRings k l D E f)
      (coefficientBase k l D E f) (targetComplete p l E hc) ≫
    (underCechModuleIso l E).inv

/-- 基底を変える Čech 代数射の、完備係数拡大後の交代余面複体の射。 -/
def completedUnderCechCoefficientCochainMap :
    ((pCompletedScalarExtensionFunctor p (algebraMap k l)).mapHomologicalComplex _).obj
      ((alternatingCofaceMapComplex (ModuleCat.{u} k)).obj (D ⋙ PDCechNerve.algebraModule k)) ⟶
    (alternatingCofaceMapComplex (ModuleCat.{u} l)).obj (E ⋙ PDCechNerve.algebraModule l) :=
  ((SerrePositivity.Cosimplicial.alternatingCofaceMapComplexCompMapHomologicalComplexIso
      (pCompletedScalarExtensionFunctor p (algebraMap k l))).app
        (D ⋙ PDCechNerve.algebraModule k)).hom ≫
    (alternatingCofaceMapComplex (ModuleCat.{u} l)).map
      (completedUnderCechCoefficientMap p k l D E f hc)

/-- 指定された半線形環射を、枠の台加群の間の関数として読む。 -/
def underCechCoefficientTermFunction (n : SimplexCategory) :
    (D ⋙ PDCechNerve.algebraModule k).obj n → (E ⋙ PDCechNerve.algebraModule l).obj n :=
  (f.app n).right

/-- 枠の完備係数射は、純テンソルの単位上で指定された半線形環射を延長する。 -/
theorem completedUnderCechCoefficientMap_unit (n : SimplexCategory) (b : l)
    (x : (D ⋙ PDCechNerve.algebraModule k).obj n) :
    (completedUnderCechCoefficientMap p k l D E f hc).app n
      (((moduleCompletionH0Unit l (p : l)).app
        ((ModuleCat.extendScalars (algebraMap k l)).obj
          ((D ⋙ PDCechNerve.algebraModule k).obj n))) (b ⊗ₜ[k,algebraMap k l] x)) =
      b • underCechCoefficientTermFunction k l D E f n x := by
  change (SerrePositivity.Cosimplicial.completedCoefficientMap p k l
      (D ⋙ Under.forget (CommRingCat.of k)) (E ⋙ Under.forget (CommRingCat.of l))
      (underCechBase k D) (underCechBase l E) (coefficientRings k l D E f)
      (coefficientBase k l D E f) (targetComplete p l E hc)).app n
        ((pCompletedScalarExtensionFunctor p (algebraMap k l)).map (𝟙 _)
          (((moduleCompletionH0Unit l (p : l)).app
            ((ModuleCat.extendScalars (algebraMap k l)).obj
              ((D ⋙ PDCechNerve.algebraModule k).obj n))) (b ⊗ₜ[k,algebraMap k l] x))) = _
  refine (congrArg
    ((SerrePositivity.Cosimplicial.completedCoefficientMap p k l
      (D ⋙ Under.forget (CommRingCat.of k)) (E ⋙ Under.forget (CommRingCat.of l))
      (underCechBase k D) (underCechBase l E) (coefficientRings k l D E f)
      (coefficientBase k l D E f) (targetComplete p l E hc)).app n)
    (ConcreteCategory.congr_hom
      ((pCompletedScalarExtensionFunctor p (algebraMap k l)).map_id _) _)).trans ?_
  exact SerrePositivity.Cosimplicial.completedCoefficientMap_unit p k l
    (D ⋙ Under.forget (CommRingCat.of k)) (E ⋙ Under.forget (CommRingCat.of l))
    (underCechBase k D) (underCechBase l E) (coefficientRings k l D E f)
    (coefficientBase k l D E f) (targetComplete p l E hc) n b x

variable {D' : SerrePositivity.Cosimplicial.CosimplicialAlgebra k}
variable {E' : SerrePositivity.Cosimplicial.CosimplicialAlgebra l}

/-- 元の厳密な代数射の正方形は、完備係数拡大後の余単体射でも厳密に可換。 -/
theorem completedUnderCechCoefficientMap_naturality (α : D ⟶ D') (β : E ⟶ E')
    (f' : D' ⟶ E' ⋙ Under.map (CommRingCat.ofHom (algebraMap k l)))
    (hc' : ∀ n, IsModuleComplete l (p : l) ((E' ⋙ PDCechNerve.algebraModule l).obj n))
    (h : α ≫ f' = f ≫ Functor.whiskerRight β
      (Under.map (CommRingCat.ofHom (algebraMap k l)))) :
    Functor.whiskerRight (Functor.whiskerRight α (PDCechNerve.algebraModule k))
        (pCompletedScalarExtensionFunctor p (algebraMap k l)) ≫
      completedUnderCechCoefficientMap p k l D' E' f' hc' =
    completedUnderCechCoefficientMap p k l D E f hc ≫
      Functor.whiskerRight β (PDCechNerve.algebraModule l) := by
  apply NatTrans.ext
  funext n
  let : Algebra k (D.obj n).right := (D.obj n).hom.hom.toAlgebra
  apply pCompletedScalarExtension_hom_ext p k l (D.obj n).right
    ((E' ⋙ PDCechNerve.algebraModule l).obj n) (hc' n)
  intro b x
  change (completedUnderCechCoefficientMap p k l D' E' f' hc').app n
      ((pCompletedScalarExtensionFunctor p (algebraMap k l)).map
        ((PDCechNerve.algebraModule k).map (α.app n)) _) =
    (PDCechNerve.algebraModule l).map (β.app n)
      ((completedUnderCechCoefficientMap p k l D E f hc).app n _)
  have hu := pCompletedScalarExtension_map_unit_linear p k l
    ((PDCechNerve.algebraModule k).map (α.app n)) b x
  refine (congrArg ((completedUnderCechCoefficientMap p k l D' E' f' hc').app n) hu).trans ?_
  refine (completedUnderCechCoefficientMap_unit p k l D' E' f' hc' n b
    ((PDCechNerve.algebraModule k).map (α.app n) x)).trans ?_
  have hr := congrArg ((PDCechNerve.algebraModule l).map (β.app n))
    (completedUnderCechCoefficientMap_unit p k l D E f hc n b x)
  have hs := ConcreteCategory.congr_hom
    (congrArg (fun t => Under.Hom.right t) (NatTrans.congr_app h n)) x
  have hs' : underCechCoefficientTermFunction k l D' E' f' n
      ((PDCechNerve.algebraModule k).map (α.app n) x) =
    (PDCechNerve.algebraModule l).map (β.app n)
      (underCechCoefficientTermFunction k l D E f n x) := hs
  refine (congrArg (b • ·) hs').trans ?_
  exact (((PDCechNerve.algebraModule l).map (β.app n)).hom.map_smul b
    (underCechCoefficientTermFunction k l D E f n x)).symm.trans hr.symm

/-- 枠の半線形な正方形の完備延長は、実際の交代余面複体でも厳密に可換。 -/
theorem completedUnderCechCoefficientCochainMap_naturality (α : D ⟶ D') (β : E ⟶ E')
    (f' : D' ⟶ E' ⋙ Under.map (CommRingCat.ofHom (algebraMap k l)))
    (hc' : ∀ n, IsModuleComplete l (p : l) ((E' ⋙ PDCechNerve.algebraModule l).obj n))
    (h : α ≫ f' = f ≫ Functor.whiskerRight β
      (Under.map (CommRingCat.ofHom (algebraMap k l)))) :
    ((pCompletedScalarExtensionFunctor p (algebraMap k l)).mapHomologicalComplex _).map
        ((alternatingCofaceMapComplex (ModuleCat.{u} k)).map
          (Functor.whiskerRight α (PDCechNerve.algebraModule k))) ≫
      completedUnderCechCoefficientCochainMap p k l D' E' f' hc' =
    completedUnderCechCoefficientCochainMap p k l D E f hc ≫
      (alternatingCofaceMapComplex (ModuleCat.{u} l)).map
        (Functor.whiskerRight β (PDCechNerve.algebraModule l)) := by
  let F := pCompletedScalarExtensionFunctor p (algebraMap k l)
  let A := alternatingCofaceMapComplex (ModuleCat.{u} l)
  let I := SerrePositivity.Cosimplicial.alternatingCofaceMapComplexCompMapHomologicalComplexIso F
  have hi := I.hom.naturality (Functor.whiskerRight α (PDCechNerve.algebraModule k))
  change (F.mapHomologicalComplex _).map
      ((alternatingCofaceMapComplex (ModuleCat.{u} k)).map
        (Functor.whiskerRight α (PDCechNerve.algebraModule k))) ≫
      (I.app (D' ⋙ PDCechNerve.algebraModule k)).hom =
    (I.app (D ⋙ PDCechNerve.algebraModule k)).hom ≫
      A.map (Functor.whiskerRight (Functor.whiskerRight α (PDCechNerve.algebraModule k)) F) at hi
  dsimp only [completedUnderCechCoefficientCochainMap]
  rw [← Category.assoc, hi, Category.assoc, ← CategoryTheory.Functor.map_comp,
    completedUnderCechCoefficientMap_naturality p k l D E f hc α β f' hc' h,
    CategoryTheory.Functor.map_comp, ← Category.assoc]

end SerrePositivity.BhattScholze.Prismatic
