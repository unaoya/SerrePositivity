module
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.WeightIntervalBoundary
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.SimplicialHomotopyEquivalence
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.ProjectiveWeightTensorLifting

/-!
概要：各値で境界右類を持つ重みの射の同じ切断と、全自然な区間収縮を作る。
方針：元の射影cofibrancyで切断を取り、同じ基底を保つ境界を区間へ持ち上げる。
規約：IS-W2 R03a.1の証明分割。元の重みの全射を保持する。
使われ方：同じ指定重み比較の右射の制限の実際のホモトピー逆。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.SSet _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.SerrePositivity.SimplicialModel.LargeParameterHomotopy
open _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open scoped _root_.Simplicial
variable (I : Type u) [SmallCategory I]

/-- 元の全重みの区間からの同じ射影。 -/
def weightIntervalProjection (V : I ⥤ SSet.{u}) :
    V ⊗ (Functor.const I).obj (Δ[1] : SSet.{u}) ⟶ V where
  app i := fst (V.obj i) (Δ[1] : SSet.{u})
  naturality i j f := rfl

/-- 元の標的重みの射影cofibrancyから得る、同じ全重みの射の切断。 -/
theorem exists_projectiveBoundary_section {V W : I ⥤ SSet.{u}} (p : V ⟶ W)
    (hp : ∀ i, SSet.modelCategoryQuillen.I.rlp (p.app i))
    (hW : (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.boundaries I).rlp.llp (initial.to W)) : ∃ s : W ⟶ V, s ≫ p = 𝟙 W := by
  letI sectionLifting := hW p ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.boundaries_rlp I).ge _ hp)
  let sq : CommSq (initial.to V) (initial.to W) p (𝟙 W) := ⟨initial.hom_ext _ _⟩
  exact ⟨sq.lift, sq.fac_right⟩

/-- 同じ切断の合成を元の恒等射へ結ぶ、全重み上の区間ホモトピー。 -/
theorem exists_projectiveBoundary_contraction {V W : I ⥤ SSet.{u}} (p : V ⟶ W)
    (hp : ∀ i, SSet.modelCategoryQuillen.I.rlp (p.app i))
    (hV : (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.boundaries I).rlp.llp (initial.to V)) (s : W ⟶ V) (hs : s ≫ p = 𝟙 W) :
    ∃ T : V ⊗ (Functor.const I).obj (Δ[1] : SSet.{u}) ⟶ V,
      _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weightIntervalZero I V ≫ T = p ≫ s ∧ _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weightIntervalOne I V ≫ T = 𝟙 V := by
  let a := _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weightIntervalBoundary I (p ≫ s) (𝟙 V)
  let b := _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weightIntervalProjection I V ≫ p
  have hw : a ≫ p = ((weightedParameterFunctor V).map ∂Δ[1].ι) ≫ b := by
    apply NatTrans.ext
    funext i
    change boundaryMap (p.app i ≫ s.app i) (𝟙 _) ≫ p.app i =
      ((V.obj i) ◁ ∂Δ[1].ι) ≫ fst (V.obj i) (Δ[1] : SSet.{u}) ≫ p.app i
    have hi := NatTrans.congr_app hs i
    change s.app i ≫ p.app i = 𝟙 _ at hi
    rw [_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight_boundaryMap_comp _ _ _ (by simp only [Category.assoc, hi,
      Category.comp_id, Category.id_comp]), Category.id_comp, whiskerLeft_fst_assoc]
  letI intervalLifting := _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.projectiveWeight_tensor_lifting I V hV ∂Δ[1].ι p hp
  let sq : CommSq a ((weightedParameterFunctor V).map ∂Δ[1].ι) p b := ⟨hw⟩
  refine ⟨sq.lift, ?_, ?_⟩
  · exact _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weightIntervalBoundary_lift_zero I _ _ _ sq.fac_left
  · exact _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weightIntervalBoundary_lift_one I _ _ _ sq.fac_left

/-- 元の境界右類の射の制限は、同じ切断と区間収縮を持つ実際のホモトピー同値。 -/
theorem weightedSectionsPre_homotopyEquivalence_of_projectiveBoundary
    {V W : I ⥤ SSet.{u}} (p : V ⟶ W)
    (hp : ∀ i, SSet.modelCategoryQuillen.I.rlp (p.app i))
    (hV : (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.boundaries I).rlp.llp (initial.to V))
    (hW : (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.boundaries I).rlp.llp (initial.to W)) (H : I ⥤ SSet.{u}) :
    IsSimplicialHomotopyEquivalence (weightedSectionsPre p H) := by
  obtain ⟨s, hs⟩ := _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.exists_projectiveBoundary_section I p hp hW
  obtain ⟨T, h₀, h₁⟩ := _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.exists_projectiveBoundary_contraction I p hp hV s hs
  refine ⟨weightedSectionsPre s H, ?_, ?_⟩
  · rw [← weightedSectionsPre_comp, hs, weightedSectionsPre_id]
    exact ⟨SSet.RelativeMorphism.Homotopy.refl (SSet.RelativeMorphism.botEquiv.symm (𝟙 _))⟩
  · rw [← weightedSectionsPre_comp]
    have ht := _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weightedSectionsPreHomotopy I T h₀ h₁ H
    rw [weightedSectionsPre_id] at ht
    exact ⟨ht⟩

end SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight
