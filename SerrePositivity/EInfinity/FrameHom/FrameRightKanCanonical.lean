module

public import SerrePositivity.EInfinity.FrameHom.FrameRightKan
public import SerrePositivity.InfinityCategories.Derived.CosliceRealizationLimitCone
public import SerrePositivity.InfinityCategories.Derived.CofinalLimitTransfer

/-!
# 同じ frame 次数比較による標準右 Kan 錐

概要：可逆な augmentation の元の coslice 実現から標準錐の極限性を得る。
方針：全 prism の後合成錐と標準錐の cofinal 制限を厳密に同定する。
規約：任意 quasicategory 標的と同じ全錐を保持する。
使われ方：元の局所化射による前合成の充満忠実性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.FrameHom.FrameArrows
open CategoryTheory Limits SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {I C : Type u} [Category.{u} I] [Category.{u} C]
  (A : I ⥤ C) {X : C} (p : A ⟶ (Functor.const I).obj X)
  {E : SSet.{u}} [Quasicategory E] (q : nerve C ⟶ E)
  (hp : ∀ i, IsInvertibleEdge ((nerve.edgeMk (p.app i)).map q).toTruncated)

lemma frameRightKanCanonicalCone_isLimit
    (hc : IsLeftCofinal (frameRightKanMap A p q hp))
    (hI : IsWeaklyContractible (nerve I)) {Z : SSet.{u}} [Quasicategory Z] (G : E ⟶ Z) :
    IsLimitCone (rightKanCanonicalCone q G (q.app (Opposite.op ⦋0⦌) (nerveVertex X))) := by
  apply (isLimitCone_iff_restrict_of_leftCofinal (frameRightKanMap A p q hp) hc _ _).mpr
  let R := frameRightKanCosliceRealization A p q hp
  have hd : IsLimitCone (R.postcompCone G) := by
    apply CosliceHomotopyRealization.postcompCone_isLimit R _ hI G
    intro a
    exact simplicialHomotopyOfFunctorEdge_vertex_isInvertible
      (FunctorIso.edge (augmentationFunctorIso A p q hp).symm)
      (FunctorIso.edge_isInvertible (augmentationFunctorIso A p q hp).symm) a
  have he : (F2.restrictJoinCone
      (rightKanCanonicalCone q G (q.app (Opposite.op ⦋0⦌) (nerveVertex X)))
      (frameRightKanMap A p q hp)).val = (R.postcompCone G).val := by
    change joinMap (𝟙 (Δ[0] : SSet.{u})) (frameRightKanMap A p q hp) ≫
      (sliceUnderUncurry (pullback.fst _ _) ≫ G) = sliceUnderUncurry R.diagram ≫ G
    rw [← Category.assoc, ← sliceUnderUncurry_precomp, frameRightKanMap_coslice]
  exact IsLimitCone.of_functorIso hd
    (eqToIso (congrArg (fun t => SSet.HomotopyCategory.mk (functorVertex t)) he.symm))

end SerrePositivity.EInfinity.FrameHom.FrameArrows
