module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictBarNativeSimplexMapAlgebra

/-!
概要：固定次元の元の HA 単体と全成分に可換する閉零写像の通常圏を作る。
方針：証明済みの厳密 HA 写像の恒等・合成を使い、元の native 単体の関手を与える。
規約：対象は固定次元の単体であり、図式圏の厳密化の同値はここでは主張しない。
使われ方：3b-3 R6、元の native 余錐の各セルの全パラメーター評価。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison

/-- 固定次元の元の HA 単体を対象とする、独立した通常圏の対象型。 -/
structure StrictSimplexCategory (A : Type u) [CommRing A] (E : Type (u + 1)) [DGCategory A E]
    (n : ℕ) where
  /-- 元の全 HA 単体。 -/
  val : Simplex A E n

instance (A : Type u) [CommRing A] (E : Type (u + 1)) [DGCategory A E] (n : ℕ) :
    Category.{u} (StrictSimplexCategory A E n) where
  Hom s t := StrictSimplexMap A E s.val.toSimplexData t.val.toSimplexData
  id s := StrictSimplexMap.id s.val.toSimplexData
  comp f g := f.comp g
  id_comp f := StrictSimplexMap.id_comp f
  comp_id f := StrictSimplexMap.comp_id f
  assoc f g h := StrictSimplexMap.comp_assoc f g h

/-- 面・退化に沿う元の HA 単体の引き戻しの通常関手。 -/
def strictSimplexPullbackFunctor (A : Type u) [CommRing A] (E : Type (u + 1)) [DGCategory A E]
    {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1)) :
    StrictSimplexCategory A E n ⥤ StrictSimplexCategory A E m where
  obj s := ⟨s.val.pullback α⟩
  map f := f.pullback α
  map_id s := StrictSimplexMap.pullback_id s.val.toSimplexData α
  map_comp f g := StrictSimplexMap.pullback_comp f g α

/-- 元の native 余錐の固定セルは、元の全 strict 図式と射の通常関手を与える。 -/
def strictBarNativeSimplexFunctor (A : Type u) [CommRing A] (J : Type) [SmallCategory J]
    {n : ℕ} (s : ((SSet.uliftFunctor.{u, 0}).obj (nerve J)) _⦋n⦌) :
    (J ⥤ ModuleCategory A PUnit.{1}) ⥤ StrictSimplexCategory A (RightModule A PUnit.{1}) (n + 1) where
  obj F := ⟨strictBarNativeSimplex A J F s⟩
  map η := strictBarNativeSimplexMap A J η s
  map_id F := strictBarNativeSimplexMap_id A J F s
  map_comp η θ := strictBarNativeSimplexMap_comp A J η θ s

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
