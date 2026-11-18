module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanActualIndexValue
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanLimitVertexTransport
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.NativePullbackRepresentationArrowComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.NativePullbackReconstructionRelativeIso
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftPullbackLimitActualArrow

/-!
概要：同じ指定同型に沿う右 Kan 添字輸送の頂点の順射は恒等射になる。
方針：同じ制限錐とその頂点等式で、指定極限比較を計算する。
規約：HTT 5.1.5.6、Kerodon Definition 7.3.1.2（Tag 02Y9）の指定輸送の比較。
使われ方：S8 の指定局所極限の値の計算。
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 同じ指定同型に沿う右 Kan 添字輸送の頂点の順射は恒等射になる。 -/
@[cite HTT "5.1.5.6" (partial := special) "右 Kan 輸送の同じ指定局所極限に沿う順射の計算。"]
lemma rightKanIndexTransport_valueHom :
∀ {K C D : SSet.{u}} [Quasicategory K] [Quasicategory C] [Quasicategory D]
  {δ δ' : K ⟶ C} (e : FunctorIso δ δ') (O : K ⟶ D) (G : C ⟶ D)
  (β : SSet.Homotopy (δ' ≫ G) O) (v : C _⦋0⦌),
  let b := (e.postcomp G).hom ≫
    Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy β)
  ∀ (s : RightKanConeTransport δ O G (functorHomHomotopy b) v)
    (t : RightKanConeTransport δ' O G β v)
    (hs : IsLimitCone s.cone) (ht : IsLimitCone t.cone),
  eqToHom (congrArg (fun x => (HomotopyCategory.mk x : hoFunctor.obj D))
      s.cone_vertex.symm) ≫
    (rightKanLimitVertexIsoOfFunctorIso e O v s.cone t.cone hs ht).hom ≫
    eqToHom (congrArg (fun x => (HomotopyCategory.mk x : hoFunctor.obj D))
      t.cone_vertex) = 𝟙 (HomotopyCategory.mk (G.app _ v)) := by
  intro K C D hK hC hD δ δ' e O G β v
  dsimp only
  intro s t hs ht
  let p := sliceUnderProjection (SSet.yonedaEquiv.symm v)
  letI : LeftFibration p := inferInstance
  letI : Quasicategory (sliceUnder (SSet.yonedaEquiv.symm v)) := quasicategory_of_innerFibration p
  let R := nativeLeftTransportRepresentation p
  obtain ⟨a, ha, L, hL, hz, ht₀, ⟨h⟩⟩ :=
    exists_nativePullbackRepresentationArrowComparison p R e
  have ea := nativePullbackArrow_isQCatEquivalence p R e a hz ht₀ h
  obtain ⟨l, _, hl⟩ := nativePullbackLift_descend_specified p R e a ha L hL
  obtain ⟨h₀, h₁, ⟨j⟩⟩ := nativePullback_reconstruction_relativeIso p R e a hz ht₀ h
  have hh := leftPullback_limitVertexIso_eq_actualArrow p R e a ha ea h₀ h₁ j O s.cone t.cone hs ht
  change (rightKanLimitVertexIsoOfFunctorIso e O v s.cone t.cone hs ht).hom = _ at hh
  rw [hh]
  exact rightKan_actualIndexArrow_valueHom e O G β v a ha l hl s t ea hs ht

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
