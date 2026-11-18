module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningBaseChangePointedPrism
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.VertexTransport.FullSubcomplexEdgeLift
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PullbackEdgeRepresentatives
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.RepresentationEdgeIso

/-!
概要：底変換の指定pointed prismを表現空間内の同型へ戻す。
方針：引き戻しの辺と全部分複体への持ち上げ、図式射影の既存の法則を使う。
規約：HTT §3.3.2（特に3.3.2.8）・Kerodon §5.6（Tag 028T）の構成の特殊な照合。
  底変換の元の同じ図式同型νを保つ。一般の分類定理全体は主張しない。
使われ方：P3-C1、scaffoldの制限と復元の底変換の照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 同じpointed prismを四角形の辺へ戻し、元の指定図式同型を保持する。
HTT §3.3.2・Kerodon Tag 028Tの構成の、この表現空間模型での法則。 -/
private lemma transportWitnessIso_of_pointedPrism {E B : SSet.{u+1}}
    (p : E ⟶ B) [LeftFibration p] (R S : LeftTransportRepresentation p)
    (ν : FunctorIso R.diagram S.diagram)
    (W : (Δ[1] : SSet.{u+1}) ⊗ E ⟶ PointedSpaceInfinity.{u})
    (h₀ : prismEndpoint 0 E ≫ W = R.pointedMap)
    (h₁ : prismEndpoint 1 E ≫ W = S.pointedMap)
    (hp : W ≫ pointedSpaceProjection = (Δ[1] ◁ p) ≫
      functorEdgePrism (functorEdgeOfSimplicialHomotopy (functorHomHomotopy ν.hom))) :
    ∃ a : VertexIso (transportWitnessVertex R) (transportWitnessVertex S),
      R.diagramIso S a = ν := by
  let H : SSet.Homotopy R.pointedMap S.pointedMap := {
    h := (β_ E (Δ[1] : SSet.{u+1})).hom ≫ W
    h₀ := by change prismEndpoint 0 E ≫ W = R.pointedMap; exact h₀
    h₁ := by change prismEndpoint 1 E ≫ W = S.pointedMap; exact h₁
    rel := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro s
      exact False.elim s.1.property }
  let a := functorEdgeOfSimplicialHomotopy H
  let b := functorEdgeOfSimplicialHomotopy (functorHomHomotopy ν.hom)
  have ha : functorFamilyPrism (SSet.yonedaEquiv.symm a.edge) = W := by
    change (β_ (Δ[1] : SSet.{u+1}) E).hom ≫
      uncurry (SSet.yonedaEquiv.symm (SSet.yonedaEquiv (curry H.h))) = W
    rw [Equiv.symm_apply_apply, uncurry_curry]
    change (β_ (Δ[1] : SSet.{u+1}) E).hom ≫
      (β_ E (Δ[1] : SSet.{u+1})).hom ≫ W = W
    rw [← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]
  let P := (ihom E).map pointedSpaceProjection
  let Q := (pre p).app SpaceInfinity.{u}
  have hab : P.app _ a.edge = Q.app _ b.edge := by
    change P.app (Opposite.op ⦋1⦌) a.edge = Q.app (Opposite.op ⦋1⦌) b.edge
    have h : SSet.yonedaEquiv.symm a.edge ≫ P = SSet.yonedaEquiv.symm b.edge ≫ Q := by
      apply functorFamilyPrism_injective (Δ[1] : SSet.{u+1}) E SpaceInfinity.{u}
      rw [functorFamilyPrism_post, functorFamilyPrism_pre, ha]
      exact hp
    have h' := congrArg SSet.yonedaEquiv h
    simp only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] at h'
    change P.app (Opposite.op ⦋1⦌) a.edge = Q.app (Opposite.op ⦋1⦌) b.edge at h'
    exact h'
  let x := transportSquareVertex R.toSquare
  let y := transportSquareVertex S.toSquare
  let a' : Truncated.Edge (X := (truncation 2).obj ((ihom E).obj PointedSpaceInfinity.{u}))
      ((pullback.fst P Q).app _ x) ((pullback.fst P Q).app _ y) := {
    edge := a.edge
    src_eq := a.src_eq.trans (transportSquareVertex_pointed R.toSquare).symm
    tgt_eq := a.tgt_eq.trans (transportSquareVertex_pointed S.toSquare).symm }
  let b' : Truncated.Edge (X := (truncation 2).obj ((ihom B).obj SpaceInfinity.{u}))
      ((pullback.snd P Q).app _ x) ((pullback.snd P Q).app _ y) := {
    edge := b.edge
    src_eq := b.src_eq.trans (transportSquareVertex_diagram R.toSquare).symm
    tgt_eq := b.tgt_eq.trans (transportSquareVertex_diagram S.toSquare).symm }
  let c := pullbackEdgeOfComponents P Q a' b' hab
  obtain ⟨f, hf⟩ := exists_fullSubcomplexEdgeLift (IsTransportWitnessVertex p)
    (transportWitnessVertex R) (transportWitnessVertex S) c
  have hd : transportWitnessSpaceDiagramEdge f = b := by
    apply Truncated.Edge.ext
    have h := congrArg Truncated.Edge.edge hf
    change (transportWitnessSpaceι p).app _ f.edge = c.edge at h
    change (pullback.snd P Q).app _ ((transportWitnessSpaceι p).app _ f.edge) = b.edge
    rw [h]
    exact congrArg Truncated.Edge.edge (pullbackEdgeOfComponents_snd P Q a' b' hab)
  refine ⟨transportWitnessSpaceEdgeIso f, ?_⟩
  apply Iso.ext
  calc
    _ = Truncated.HomotopyCategory.homMk (transportWitnessSpaceDiagramEdge f) :=
      (transportWitnessSpaceDiagramEdge_hom f).symm
    _ = Truncated.HomotopyCategory.homMk b := congrArg Truncated.HomotopyCategory.homMk hd
    _ = ν.hom := functorHomHomotopy_hom ν.hom

/-- 底変換の二つの表現は、元の指定図式同型νを保つ同じwitnessで結ばれる。
HTT §3.3.2・Kerodon Tag 028Tの構成の、指定scaffoldによる特殊な照合。 -/
@[cite HTT "3.3.2" (partial := special) "指定pointed prismから得る底変換witnessと元の分類同型の一致。"]
lemma leftStraighteningBaseChange_transportWitness :
    ∀ {E B D : SSet.{u}} [Quasicategory B] [Quasicategory D]
  (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B),
  let U := SSet.uliftFunctor.{u+1,u}
  let lB := transportSimplexFirstVertexMap B
  let lD := transportSimplexFirstVertexMap D
  let H := transportSimplexFunctor k
  let q := pullback.snd p k
  let p₀ := pullback.snd p lB
  let r := pullback.snd q lD
  let d := leftStraighteningBaseChangePullbackData p k
  let R₀ := (nerveLeftTransportRepresentation p₀).cartesianRestrict
    (U.map d.val) (U.map (nerveMap H)) d.property.2.2.2
  let Rr := nerveLeftTransportRepresentation r
  let θp := leftStraighteningInfinityDiagram_firstVertexTransportIso p
  let θq := leftStraighteningInfinityDiagram_firstVertexTransportIso q
  let β := leftStraighteningInfinityDiagram_baseChangeIso p k
  let ν := (θp.precomp (U.map (nerveMap H))).symm ≪≫
    diagramIsoCongr
      (by rw [← Category.assoc, ← transportSimplexFirstVertexMap_ulift_naturality k,
        Category.assoc]) rfl (β.precomp (U.map lD)) ≪≫ θq
  ∃ a : VertexIso (transportWitnessVertex R₀) (transportWitnessVertex Rr),
    R₀.diagramIso Rr a = ν := by
  intro E B D hB hD p hp k
  let U := SSet.uliftFunctor.{u+1,u}
  let lB := transportSimplexFirstVertexMap B
  let lD := transportSimplexFirstVertexMap D
  let H := transportSimplexFunctor k
  let q := pullback.snd p k
  let p₀ := pullback.snd p lB
  let r := pullback.snd q lD
  let d := leftStraighteningBaseChangePullbackData p k
  let R₀ := (nerveLeftTransportRepresentation p₀).cartesianRestrict
    (U.map d.val) (U.map (nerveMap H)) d.property.2.2.2
  let Rr := nerveLeftTransportRepresentation r
  let θp := leftStraighteningInfinityDiagram_firstVertexTransportIso p
  let θq := leftStraighteningInfinityDiagram_firstVertexTransportIso q
  let β := leftStraighteningInfinityDiagram_baseChangeIso p k
  let ν : FunctorIso (U.map (nerveMap H) ≫ leftCoherentTransport p₀)
      (leftCoherentTransport r) := (θp.precomp (U.map (nerveMap H))).symm ≪≫
    diagramIsoCongr
      (by rw [← Category.assoc, ← transportSimplexFirstVertexMap_ulift_naturality k,
        Category.assoc]) rfl (β.precomp (U.map lD)) ≪≫ θq
  obtain ⟨W, h₀, h₁, hpW⟩ := leftStraighteningBaseChange_pointedPrism p k
  exact transportWitnessIso_of_pointedPrism (U.map r) R₀ Rr ν W h₀ h₁ hpW

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
