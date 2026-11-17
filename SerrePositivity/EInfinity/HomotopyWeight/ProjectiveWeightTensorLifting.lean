module
public import SerrePositivity.EInfinity.HomotopyWeight.NativeWeightedSections

/-!
概要：射影cofibrant重みと単射パラメーターのテンソルは、点ごとの境界右類を持ち上げる。
方針：同じ二変数随伴に初期重みを入れ、単射のpushout-productの法則を移す。
規約：IS-W2 R03a.1の切断と区間収縮の証明分割。
使われ方：同じ元の重み全体の境界から区間への持ち上げ。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.HomotopyWeight
open CategoryTheory Limits SSet MonoidalCategory HomotopicalAlgebra
open SerrePositivity.PointwiseAdjunction
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open scoped Simplicial
variable (I : Type u) [SmallCategory I]

/-- 元の重みと単射の同じテンソルは、各値の境界右類に対して左持ち上げ性。 -/
theorem projectiveWeight_tensor_lifting (W : I ⥤ SSet.{u})
    (hW : (boundaries I).rlp.llp (initial.to W))
    {A B : SSet.{u}} (f : A ⟶ B) [Mono f] {F G : I ⥤ SSet.{u}} (p : F ⟶ G)
    (hp : ∀ i, SSet.modelCategoryQuillen.I.rlp (p.app i)) :
    HasLiftingProperty ((weightedParameterFunctor W).map f) p := by
  let baseAdj := ParametrizedAdjunctionTransport.left MonoidalClosed.internalHomAdjunction₂
    (BraidedCategory.curriedBraidingNatIso SSet.{u})
  let adj := PointwiseAdjunction.adjunction I baseAdj
  let (T : SSet.{u}) : ((pointwise I (curriedTensor SSet.{u}).flip).obj T).IsLeftAdjoint :=
    (adj.adj T).isLeftAdjoint
  let push := Functor.PushoutObjObj.ofIsInitialRight
    (pointwise I (curriedTensor SSet.{u}).flip) f (initial.to W) initialIsInitial
  let pull := Functor.PullbackObjObj.ofHasPullback
    (pointwise I (MonoidalClosed.internalHom (C := SSet.{u}))) f p
  apply (adj.hasLiftingProperty_iff push pull).mpr
  apply hW
  rw [boundaries_rlp]
  intro i X Y j hj
  have jMono : Mono j := SSet.modelCategoryQuillen.I_le_monomorphisms _ hj
  letI := jMono
  let sq := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) j f
  apply (baseAdj.hasLiftingProperty_iff sq.flip
    (evaluatePullbackObjObj I _ f p pull i)).mp
  have productMono : Mono sq.ι := SimplicialModel.simplicial_pushoutProduct_mono j f sq
  exact SSet.rlp_monomorphisms.ge _ (hp i) sq.ι productMono

end SerrePositivity.EInfinity.HomotopyWeight
