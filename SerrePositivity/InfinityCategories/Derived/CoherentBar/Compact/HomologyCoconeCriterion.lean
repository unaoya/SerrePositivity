module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.HomologyBarNondegAugmentationLegs
/-!
概要：評価ホモロジーの余錐を、非退化 bar の実増大の余核性で判定する。
方針：各零単体で増大が元の脚であることを使い、余核の普遍性を余錐へ戻す。
規約：元の余錐の全脚を保持し、頂点だけの比較では済ませない。
使われ方：coherent bar の C1 を native 余錐の評価に適用する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits Opposite SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] {J : Type u} [PartialOrder J]
  (F : J ⥤ ModuleCat.{u} R) (c : Cocone F)

def dgBarCompactHomologyCocone_isColimit_of_cokernel
    (h : IsColimit (CokernelCofork.ofπ (dgHomologyBarNondegAugmentation R F c)
      (dgHomologyBarNondegAugmentation_d_one R F c))) : IsColimit c := by
  let desc (s : Cocone F) := h.desc
    (CokernelCofork.ofπ (dgHomologyBarNondegAugmentation R F s)
      (dgHomologyBarNondegAugmentation_d_one R F s))
  have hd (s : Cocone F) : dgHomologyBarNondegAugmentation R F c ≫ desc s =
      dgHomologyBarNondegAugmentation R F s := Cofork.IsColimit.π_desc h
  refine { desc := desc, fac := ?_, uniq := ?_ }
  · intro s j
    let t : (nerve J).nonDegenerate 0 :=
      ⟨nerveEquiv.symm j, by rw [SSet.nondegenerate_zero]; trivial⟩
    have e := congrArg (fun f => Sigma.ι (dgHomologyBarNondegFamily R F 0) t ≫ f) (hd s)
    simpa only [← Category.assoc, dgHomologyBarNondegAugmentation_ι] using! e
  · intro s m hm
    apply Cofork.IsColimit.hom_ext h
    change dgHomologyBarNondegAugmentation R F c ≫ m =
      dgHomologyBarNondegAugmentation R F c ≫ desc s
    rw [hd]
    apply Sigma.hom_ext
    intro t
    rw [← Category.assoc, dgHomologyBarNondegAugmentation_ι,
      dgHomologyBarNondegAugmentation_ι, hm]

lemma dgBarCompactHomologyCocone_isColimit_iff_cokernel :
    Nonempty (IsColimit c) ↔ Nonempty (IsColimit (CokernelCofork.ofπ
      (dgHomologyBarNondegAugmentation R F c)
      (dgHomologyBarNondegAugmentation_d_one R F c))) :=
  ⟨fun ⟨h⟩ => ⟨dgHomologyBarNondegAugmentationIsCokernel R F c h⟩,
   fun ⟨h⟩ => ⟨dgBarCompactHomologyCocone_isColimit_of_cokernel R F c h⟩⟩

end SerrePositivity.InfinityCategories
