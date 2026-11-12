module

public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
import all Mathlib.Algebra.Homology.Additive

/-!
# 増大鎖複体の加法関手との比較

## 概要
増大の鎖写像を加法関手で写すと、写した増大対象の同じ鎖増大と両立する。

## 方針
交代面複体と single の標準比較を用い、次数零の増大射を照合する。

## 規約
増大射そのものを比較する。評価ごとの擬同型から前層圏での擬同型を検出する。

## 使われ方
Weibel §2.2、HA 1.2.4。重みの各評価の収縮から全前層の増大完全性を得る。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u v' u' w t
open CategoryTheory CategoryTheory.Limits AlgebraicTopology HomologicalComplex
open scoped Simplicial
namespace SerrePositivity.HomologicalAlgebra

/-- 同じ増大鎖写像は、加法関手と交代面・single の二つの標準比較に両立する。 -/
theorem augmentedChainMap_comparison
    {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
    {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
    (F : C ⥤ D) [F.Additive] (X : SimplicialObject.Augmented C) :
    (F.mapHomologicalComplex (.down ℕ)).map (AlternatingFaceMapComplex.ε.app X) ≫
        (singleMapHomologicalComplex F (.down ℕ) 0).hom.app X.right =
      (alternatingFaceMapComplexCompMapHomologicalComplexIso F).hom.app X.left ≫
        AlternatingFaceMapComplex.ε.app
          (((SimplicialObject.Augmented.whiskering C D).obj F).obj X) := by
  apply HomologicalComplex.to_single_hom_ext
  simp [singleMapHomologicalComplex_hom_app_self, singleObjXSelf, singleObjXIsoOfEq,
    alternatingFaceMapComplexCompMapHomologicalComplexIso]
  simp [SimplicialObject.Augmented.whiskering, SimplicialObject.Augmented.whiskeringObj]

/-- 前層圏の増大鎖写像は、各評価の extra degeneracy によって擬同型となる。 -/
theorem augmentedChain_quasiIso_of_evaluationExtraDegeneracy
    {T : Type t} [Category.{w} T] {C : Type u} [Category.{v} C] [Abelian C]
    (X : SimplicialObject.Augmented (T ⥤ C))
    (ed : ∀ t : T, SimplicialObject.Augmented.ExtraDegeneracy
      (((SimplicialObject.Augmented.whiskering (T ⥤ C) C).obj
        ((evaluation T C).obj t)).obj X)) : QuasiIso (AlternatingFaceMapComplex.ε.app X) := by
  apply (HomologicalComplex.quasiIso_iff_evaluation _).2
  intro t
  let F := (evaluation T C).obj t
  let a := (alternatingFaceMapComplexCompMapHomologicalComplexIso F).app X.left
  let b := (singleMapHomologicalComplex F (.down ℕ) 0).app X.right
  have : QuasiIso (AlternatingFaceMapComplex.ε.app
      (((SimplicialObject.Augmented.whiskering (T ⥤ C) C).obj F).obj X)) :=
    inferInstanceAs (QuasiIso (ed t).homotopyEquiv.hom)
  have hq : QuasiIso ((F.mapHomologicalComplex (.down ℕ)).map
      (AlternatingFaceMapComplex.ε.app X) ≫ b.hom) := by
    rw [show (F.mapHomologicalComplex (.down ℕ)).map (AlternatingFaceMapComplex.ε.app X) ≫
      b.hom = a.hom ≫ _ from augmentedChainMap_comparison F X]
    infer_instance
  exact (quasiIso_iff_comp_right _ b.hom).mp hq

end SerrePositivity.HomologicalAlgebra
