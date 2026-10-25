module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.HomologyBarDegreeOne

/-!
概要：一次境界を消す bar の零次写像から、元の図式の余錐を回収する。
方針：元の各辺の境界関係を使い、頂点係数への制限の自然性を示す。
規約：同じホモロジー図式 F と同じ bar を使う。
使われ方：零次ホモロジーと余極限の普遍性の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits Opposite SSet AlgebraicTopology
open scoped Simplicial
variable (R : Type u) [CommRing R] {J : Type u} [PartialOrder J]
  (F : J ⥤ ModuleCat.{u} R)

lemma dgHomologyBarAugmentation_d_one (c : Cocone F) :
    (dgHomologyBarComplex R F).d 1 0 ≫
      dgHomologyBarAugmentationComponent R F c (op ⦋0⦌) = 0 := by
  have h (i : Fin 2) : (dgHomologyBarSimplicial R F).δ i ≫
      dgHomologyBarAugmentationComponent R F c (op ⦋0⦌) =
        dgHomologyBarAugmentationComponent R F c (op ⦋1⦌) := by
    simpa only [dgHomologyBarAugmentation, Functor.const_obj_map, Category.comp_id] using!
      (dgHomologyBarAugmentation R F c).naturality (SimplexCategory.δ i).op
  rw [dgHomologyBarDifferential_one, Preadditive.sub_comp, h 0, h 1, sub_self]

def dgHomologyBarCoconeOfBoundaryZero {P : ModuleCat R}
    (g : (dgHomologyBarComplex R F).X 0 ⟶ P)
    (hg : (dgHomologyBarComplex R F).d 1 0 ≫ g = 0) : Cocone F where
  pt := P
  ι :=
    { app j := dgHomologyBarVertex R F j ≫ g
      naturality j k f := by
        have h := congrArg (fun w =>
          Sigma.ι (dgHomologyBarFamily R F (op ⦋1⦌)) (CategoryTheory.nerve.edgeMk f).edge ≫ w) hg
        erw [← Category.assoc, dgHomologyBarEdge_d, Preadditive.sub_comp,
          comp_zero, sub_eq_zero] at h
        simpa only [Category.assoc, Functor.const_obj_map, Category.comp_id] using! h }

end SerrePositivity.InfinityCategories
