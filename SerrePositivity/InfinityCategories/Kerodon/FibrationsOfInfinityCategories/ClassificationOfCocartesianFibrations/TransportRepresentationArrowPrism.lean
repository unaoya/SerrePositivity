module

public meta import SerrePositivity.Util.Citation

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.UnstraighteningSourceFamilyComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FunctorFamilyVertices
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallUnstraighteningIsoHom
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.WitnessPrism
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.WitnessPointedDiagramIso
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorIsoEdgeRepresentative
/-!
概要：同じ指定pointed prismによる表現間の射を、元のunstraighteningの作用へ比較する。
方針：既存のunstraighteningSourceFamilyComparisonIsoに同じprismの定値な零単体族を入れる。
規約：HTT §3.3.2、Kerodon Remark 5.6.2.18（Tag 0271）の既存構成の照合。
  始域と終域の全空間を同じものに限定せず、指定された底上の射aを保持する。
使われ方：R04-PRの大きい宇宙での証明分割。小さい相対関手空間への降下は別ファイル。
-/

@[expose] public noncomputable section
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 同じpointed prismの終点は、元の指定変換のunstraighteningの像と相対的に同型。 -/
@[cite HTT "3.3.2" (partial := special) "既存の全パラメーター比較を指定prismの零単体族へ適用する法則。"]
lemma transportRepresentation_arrowPrismComparison {E F B : SSet.{u + 1}}
    (p : E ⟶ B) (qF : F ⟶ B) [LeftFibration p] [LeftFibration qF]
    (R : LeftTransportRepresentation p) (S : LeftTransportRepresentation qF)
    (a : E ⟶ F) (ha : a ≫ qF = p) (ν : FunctorIso R.diagram S.diagram)
    (W : (Δ[1] : SSet.{u + 1}) ⊗ E ⟶ PointedSpaceInfinity.{u})
    (h₀ : prismEndpoint 0 E ≫ W = R.pointedMap)
    (h₁ : prismEndpoint 1 E ≫ W = a ≫ S.pointedMap)
    (hW : W ≫ pointedSpaceProjection = (Δ[1] ◁ p) ≫
      functorEdgePrism (SSet.Edge.ofTruncated (functorEdgeOfSimplicialHomotopy
        (functorHomHomotopy ν.hom)))) :
    let c := SSet.Edge.ofTruncated (functorEdgeOfSimplicialHomotopy (functorHomHomotopy ν.hom))
    let g := leftUnstraighteningMappingVertexMap R.diagram S.diagram (intervalMappingVertexOfEdge c)
    let z := R.comparison ≫ g.val
    ∃ (hz : z ≫ leftUnstraighteningProjection S.diagram = p)
      (ht : (a ≫ S.comparison) ≫ leftUnstraighteningProjection S.diagram = p),
      Nonempty (VertexIso
        (relativeFunctorVertex (leftUnstraighteningProjection S.diagram) p z hz)
        (relativeFunctorVertex (leftUnstraighteningProjection S.diagram) p (a ≫ S.comparison) ht)) := by
  dsimp only
  let e := SSet.Edge.ofTruncated (functorEdgeOfSimplicialHomotopy
    (functorHomHomotopy ν.hom))
  let z := intervalMappingVertexOfEdge e
  let g := leftUnstraighteningMappingVertexMap R.diagram S.diagram z
  let q := leftUnstraighteningProjection S.diagram
  have hf : (R.comparison ≫ g.val) ≫ q = p := by
    rw [Category.assoc, g.property, R.over_base]
  have ht : (a ≫ S.comparison) ≫ q = p := by
    rw [Category.assoc, S.over_base, ha]
  refine ⟨hf, ht, ?_⟩
  let K : SSet.{u + 1} := Δ[0]
  let t : K ⟶ leftUnstraighteningTransformationSpace R.diagram S.diagram := SSet.const z
  let f : E ⊗ K ⟶ leftUnstraightening S.diagram := fst E K ≫ (a ≫ S.comparison)
  have hfp : f ≫ q = fst E K ≫ p := by rw [Category.assoc, ht]
  let W' := fst (Δ[1] ⊗ E) K ≫ W
  have h₀' : (prismEndpoint 0 E ▷ K) ≫ W' =
      fst E K ≫ R.comparison ≫ pullback.fst pointedSpaceProjection R.diagram := by
    change (prismEndpoint 0 E ▷ K) ≫ (fst (Δ[1] ⊗ E) K ≫ W) = _
    rw [whiskerRight_fst_assoc, h₀]
    rfl
  have h₁' : (prismEndpoint 1 E ▷ K) ≫ W' =
      f ≫ pullback.fst pointedSpaceProjection S.diagram := by
    change (prismEndpoint 1 E ▷ K) ≫ (fst (Δ[1] ⊗ E) K ≫ W) = _
    rw [whiskerRight_fst_assoc, h₁]
    rfl
  have hW' : W' ≫ pointedSpaceProjection =
      ((Δ[1] ◁ p) ▷ K) ≫ functorParameterizedPrism (intervalMappingUncurry t) := by
    rw [Category.assoc, hW]
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨a, x⟩, y⟩
    rfl
  let H := unstraighteningSourceFamilyComparisonIso R.diagram S.diagram p
    R.comparison R.over_base t f hfp W' h₀' h₁' hW'
  let v0 := stdSimplex.obj₀Equiv.symm (0 : Fin 1)
  have vl : ((t ≫ leftUnstraighteningMappingSpaceMap R.diagram S.diagram) ≫
      relativeFunctorOverPre q
        (Over.homMk (U := Over.mk p) (V := Over.mk (leftUnstraighteningProjection R.diagram))
          R.comparison R.over_base)).app (Opposite.op ⦋0⦌) v0 =
      relativeFunctorVertex q p (R.comparison ≫ g.val) hf := by
    change SSet.yonedaEquiv ((t ≫ leftUnstraighteningMappingSpaceMap R.diagram S.diagram) ≫
      relativeFunctorOverPre q (Over.homMk (U := Over.mk p)
        (V := Over.mk (leftUnstraighteningProjection R.diagram)) R.comparison R.over_base)) = _
    rw [show t = SSet.const z from rfl, SSet.const_comp, SSet.const_comp, SSet.yonedaEquiv_const,
      ← leftUnstraighteningMappingVertexMap_vertex]
    exact relativeFunctorOverPre_vertex (leftUnstraighteningProjection S.diagram)
      (Over.homMk (U := Over.mk p) (V := Over.mk (leftUnstraighteningProjection R.diagram))
        R.comparison R.over_base) g.val g.property
  have vr : (relativeFunctorCurry f hfp).app (Opposite.op ⦋0⦌) v0 =
      relativeFunctorVertex q p (a ≫ S.comparison) ht := by
    rw [relativeFunctorCurry_vertex]
    apply Subtype.ext
    apply congrArg functorVertex
    dsimp only [f]
    rw [← Category.assoc, lift_fst, Category.id_comp]
  exact ⟨(eqToIso (congrArg HomotopyCategory.mk vl)).symm ≪≫
    H.app v0 ≪≫ eqToIso (congrArg HomotopyCategory.mk vr)⟩


end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
