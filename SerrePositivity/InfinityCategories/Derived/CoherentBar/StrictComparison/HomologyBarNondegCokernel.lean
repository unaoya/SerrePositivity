module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.HomologyBarSplitting

/-!
概要：非退化 H(G) bar の標準増大も一次微分の余核である。
方針：splitting の相互射と零次数で恒等な正規化射影で通常の bar の余核を移す。
規約：filtered 性は不要で、与えた余錐の全ての脚を使う。
使われ方：strict 標準増大のホモロジー射の擬同型判定。
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
  (F : J ⥤ ModuleCat.{u} R) (c : Cocone F)

def dgHomologyBarNondegAugmentation : (dgHomologyBarNondegComplex R F).X 0 ⟶ c.pt :=
  (dgHomologyBarSplitting R F).fromNondegComplex.f 0 ≫
    dgHomologyBarAugmentationComponent R F c (op ⦋0⦌)

lemma dgHomologyBarNondegAugmentation_d_one :
    (dgHomologyBarNondegComplex R F).d 1 0 ≫ dgHomologyBarNondegAugmentation R F c = 0 := by
  unfold dgHomologyBarNondegAugmentation
  rw [← Category.assoc, ← (dgHomologyBarSplitting R F).fromNondegComplex.comm 1 0,
    Category.assoc, dgHomologyBarAugmentation_d_one, comp_zero]

lemma dgHomologyBarToNondeg_augmentation :
    (dgHomologyBarSplitting R F).toNondegComplex.f 0 ≫
      dgHomologyBarNondegAugmentation R F c =
        dgHomologyBarAugmentationComponent R F c (op ⦋0⦌) := by
  unfold dgHomologyBarNondegAugmentation
  rw [← Category.assoc, ← HomologicalComplex.comp_f,
    SimplicialObject.Splitting.toNondegComplex_fromNondegComplex,
    AlgebraicTopology.DoldKan.PInfty_f_0, Category.id_comp]

def dgHomologyBarNondegAugmentationIsCokernel (hc : IsColimit c) :
    IsColimit (CokernelCofork.ofπ (dgHomologyBarNondegAugmentation R F c)
      (dgHomologyBarNondegAugmentation_d_one R F c)) := by
  let h := dgHomologyBarAugmentationIsCokernel R F c hc
  letI : Epi (dgHomologyBarAugmentationComponent R F c (op ⦋0⦌)) :=
    epi_of_isColimit_cofork h
  refine CokernelCofork.IsColimit.ofπ _ _
    (fun g hg => h.desc (CokernelCofork.ofπ
      ((dgHomologyBarSplitting R F).toNondegComplex.f 0 ≫ g) (by
        rw [← Category.assoc, ← (dgHomologyBarSplitting R F).toNondegComplex.comm 1 0,
          Category.assoc, hg, comp_zero]))) ?_ ?_
  · intro P g hg
    have hf : dgHomologyBarAugmentationComponent R F c (op ⦋0⦌) ≫
        h.desc (CokernelCofork.ofπ
      ((dgHomologyBarSplitting R F).toNondegComplex.f 0 ≫ g) (by
        rw [← Category.assoc, ← (dgHomologyBarSplitting R F).toNondegComplex.comm 1 0,
          Category.assoc, hg, comp_zero])) =
        (dgHomologyBarSplitting R F).toNondegComplex.f 0 ≫ g :=
      Cofork.IsColimit.π_desc h
    unfold dgHomologyBarNondegAugmentation
    rw [Category.assoc, hf, ← Category.assoc, ← HomologicalComplex.comp_f,
      SimplicialObject.Splitting.fromNondegComplex_toNondegComplex,
      HomologicalComplex.id_f, Category.id_comp]
  · intro P g hg m hm
    apply (cancel_epi (dgHomologyBarAugmentationComponent R F c (op ⦋0⦌))).mp
    have hf : dgHomologyBarAugmentationComponent R F c (op ⦋0⦌) ≫
        h.desc (CokernelCofork.ofπ
      ((dgHomologyBarSplitting R F).toNondegComplex.f 0 ≫ g) (by
        rw [← Category.assoc, ← (dgHomologyBarSplitting R F).toNondegComplex.comm 1 0,
          Category.assoc, hg, comp_zero])) =
        (dgHomologyBarSplitting R F).toNondegComplex.f 0 ≫ g :=
      Cofork.IsColimit.π_desc h
    rw [hf, ← hm, ← Category.assoc, dgHomologyBarToNondeg_augmentation]

end SerrePositivity.InfinityCategories
