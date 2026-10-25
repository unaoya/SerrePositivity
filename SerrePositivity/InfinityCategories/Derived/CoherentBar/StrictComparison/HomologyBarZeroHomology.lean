module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.HomologyBarCokernel
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
概要：通常のホモロジー bar の零次ホモロジーは元の図式の余極限である。
方針：零次では出る微分が零なので、検証済みの cokernel を左ホモロジーデータにする。
規約：filtered 性は不要。元の余極限の脚を持つ標準増大を使う。
使われ方：coherent bar の単体次元フィルトレーションの零次成分。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits Opposite SSet AlgebraicTopology HomologicalComplex
open scoped Simplicial
variable (R : Type u) [CommRing R] {J : Type u} [PartialOrder J]
  (F : J ⥤ ModuleCat.{u} R)

def dgHomologyBarZeroHomologyIso (c : Cocone F) (hc : IsColimit c) :
    (dgHomologyBarComplex R F).homology 0 ≅ c.pt := by
  let K := dgHomologyBarComplex R F
  have hg : (K.sc' 1 0 0).g = 0 := by
    change K.d 0 0 = 0
    exact K.shape 0 0 (by simp)
  exact K.homologyIsoSc' 1 0 0 (by simp) (by simp) ≪≫
    (ShortComplex.LeftHomologyData.ofIsColimitCokernelCofork (K.sc' 1 0 0) hg
    (CokernelCofork.ofπ (dgHomologyBarAugmentationComponent R F c (op ⦋0⦌))
      (dgHomologyBarAugmentation_d_one R F c))
    (dgHomologyBarAugmentationIsCokernel R F c hc)).homologyIso

def dgHomologyBarZeroHomologyColimitIso :
    (dgHomologyBarComplex R F).homology 0 ≅ colimit F :=
  dgHomologyBarZeroHomologyIso R F (colimit.cocone F) (colimit.isColimit F)

end SerrePositivity.InfinityCategories
