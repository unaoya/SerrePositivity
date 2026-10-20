module

public import SerrePositivity.InfinityCategories.HomotopyLimits.QuillenCfUnitPrism
public import SerrePositivity.InfinityCategories.HomotopyLimits.QuillenCfFullyFaithful
public import SerrePositivity.InfinityCategories.HomotopyLimits.IntervalUnitCollageComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.CartesianComparisonComposition
public import SerrePositivity.InfinityCategories.HomotopyLimits.HomotopyMappingEquivalence
public import SerrePositivity.InfinityCategories.F1B.UnitMappingAdjunction

/-!
概要：元の Quillen cf 輸送の同じ単位を使う、cf nerve 間の ∞ 随伴。
方針：元の辺と正方形を保持して、標準の写像空間比較へ移す。
規約：元の cf 置換との比較は別工程。使われ方：HTT 5.2.4.6 と QuillenCfDerivedLimits。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open HomotopicalAlgebra
open SerrePositivity.InfinityCategories.Coherent
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {C D : Type v} [Category.{u} C] [Category.{u} D]
  [SimplicialCategory C] [SimplicialCategory D] [ModelCategory C] [ModelCategory D]
  (R : EnrichedFunctor SSet.{u} D C)
  {L : C ⥤ D} (adj : L ⊣ coherentEnrichedUnderlyingFunctor R)
  [SerrePositivity.Quillen.IsLeftQuillen L]
  (fibD : MorphismProperty.FunctorialFactorizationData
    (trivialCofibrations D) (fibrations D))
  (e : EnrichedAdjunctionHomComposition R adj)
  (SC : SerrePositivity.Enriched.TensorCotensor SSet.{u} C)
  (SD : SerrePositivity.Enriched.TensorCotensor SSet.{u} D)
  [FixedSimplicialPushoutProduct SC.tensor] [FixedSimplicialPushoutProduct SD.tensor]
  (cofC : MorphismProperty.FunctorialFactorizationData
    (cofibrations C) (trivialFibrations C))

include fibD e SC SD cofC in
/-- 元の同じ η・左右輸送・比較正方形から、標準単位の写像空間条件を証明する。 -/
lemma quillenCfDerivedUnitMappingSpaceCondition_exists :
    letI := cofibrantFibrantObjects_nerve_quasicategory SC
    letI := cofibrantFibrantObjects_nerve_quasicategory SD
    ∃ H : SSet.Homotopy (𝟙 (SimplicialNerve (CofibrantFibrantObjects C)))
      (quillenCfLeftDerived R adj fibD e SC SD ≫ quillenCfRightDerived R adj SC SD cofC),
      UnitMappingSpaceCondition
        (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H)) := by
  have := cofibrantFibrantObjects_nerve_quasicategory SC
  have := cofibrantFibrantObjects_nerve_quasicategory SD
  have := quillenCfCollageInfinity_quasicategory R adj SC SD
  let F := quillenCfLeftDerived R adj fibD e SC SD
  let G := quillenCfRightDerived R adj SC SD cofC
  let i := quillenCfCollageBottomNerve R
  let j := quillenCfCollageTopNerve R
  let p := quillenCfCollageProjection R
  obtain ⟨η, HL, HR, J, hη0, hη1, hηi, hL0, hL1, hLp, hLc,
    hR0, hR1, hRp, hRc, hJb, hJ1, hJp, hJc⟩ :=
    quillenCfDerivedUnitPrism_exists R adj fibD e SC SD cofC
  let Hu := homotopyOfPrism η hη0 hη1
  let Hl := homotopyOfPrism HL hL0 hL1
  let Hr := homotopyOfPrism HR hR0 hR1
  refine ⟨Hu, (unitMappingSpaceCondition_iff_interval _).mpr ?_⟩
  intro x y
  let lx := functorHomEvaluate (SSet.Truncated.HomotopyCategory.homMk
    (functorEdgeOfSimplicialHomotopy Hl)) x
  have hc := cartesianComparison_component_comp F G i j η hη0 hη1 HL hL0 hL1
    HR hR0 hR1 J hηi hJb hJ1 x
  apply unitIntervalMap_isSimplicialHomotopyEquivalence_of_collage
    (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy Hu))
    i j Hr x y lx hc
  · have hmap := intervalFunctorMap_isSimplicialHomotopyEquivalence_of_fullyFaithful j
      (quillenCfCollageTopNerve_isFullyFaithful R adj SC SD)
      (F.app (Opposite.op ⦋0⦌) x) y
    have hcL : ∀ z, IsCocartesianEdge p (simplicialHomotopyVertexEdge Hl z).edge := by
      intro z
      rw [homotopyOfPrism_vertexEdge]
      exact hLc z
    have hy : p.app (Opposite.op ⦋0⦌) (j.app (Opposite.op ⦋0⦌) y) =
        stdSimplex.obj₀Equiv.symm (1 : Fin 2) := by
      exact congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) y) (quillenCfCollageTop_projection R)
    have hpre := intervalPrecompose_equivalence_of_cocartesianHomotopy Hl p
      (homotopyOfPrism_projection HL hL0 hL1 p hLp) hcL x (j.app (Opposite.op ⦋0⦌) y) hy
    exact (hmap.isQCatEquivalence.comp hpre.isQCatEquivalence).isSimplicialHomotopyEquivalence
  · have hmap := intervalFunctorMap_isSimplicialHomotopyEquivalence_of_fullyFaithful i
      (quillenCfCollageBottomNerve_isFullyFaithful R adj SC SD)
      x (G.app (Opposite.op ⦋0⦌) y)
    have hcR : ∀ z, IsCartesianEdge p (simplicialHomotopyVertexEdge Hr z).edge := by
      intro z
      rw [homotopyOfPrism_vertexEdge]
      exact hRc z
    have hx : p.app (Opposite.op ⦋0⦌) (i.app (Opposite.op ⦋0⦌) x) =
        stdSimplex.obj₀Equiv.symm (0 : Fin 2) := by
      exact congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) x) (quillenCfCollageBottom_projection R)
    have hpost := intervalPostcompose_equivalence_of_cartesianHomotopy Hr p
      (homotopyOfPrism_projection HR hR0 hR1 p hRp) hcR y (i.app (Opposite.op ⦋0⦌) x) hx
    exact (hmap.isQCatEquivalence.comp hpost.isQCatEquivalence).isSimplicialHomotopyEquivalence

include fibD e SC SD cofC in
/-- 同じ標準単位を持つ cf nerve 間の導来 ∞ 随伴。余単位・両三角恒等式を含む。 -/
lemma quillenCfDerivedAdjunction_exists :
    letI := cofibrantFibrantObjects_nerve_quasicategory SC
    letI := cofibrantFibrantObjects_nerve_quasicategory SD
    ∃ H : SSet.Homotopy (𝟙 (SimplicialNerve (CofibrantFibrantObjects C)))
      (quillenCfLeftDerived R adj fibD e SC SD ≫ quillenCfRightDerived R adj SC SD cofC),
      ∃ a : QCatAdjunction (quillenCfLeftDerived R adj fibD e SC SD)
        (quillenCfRightDerived R adj SC SD cofC),
        a.unitHom = SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H) := by
  have := cofibrantFibrantObjects_nerve_quasicategory SC
  have := cofibrantFibrantObjects_nerve_quasicategory SD
  obtain ⟨H, hH⟩ := quillenCfDerivedUnitMappingSpaceCondition_exists R adj fibD e SC SD cofC
  exact ⟨H, qcatAdjunctionOfUnitMappingSpaceCondition _ hH,
    qcatAdjunctionOfUnitMappingSpaceCondition_unitHom _ hH⟩

end
end SerrePositivity.InfinityCategories.HomotopyLimits
