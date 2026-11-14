module

public import SerrePositivity.KST.NonConnective.SequentialCofibrantColimit
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FunctorComparison.OrdinaryCoherentNatTransPrism
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.KanDiagramColimitTransport

/-!
概要：元の逐次 BF 図式の厳密な自然変換を、成分を保った coherent な同型にする。
方針：サイズを明示した nerve 上で自然変換の prism を構成し、点ごとの可逆性を使う。
規約：図式間の同値を追加仮定として置かず、実際の比較射から構成する。
使われ方：置換列の実余極限余錐を元の列へ輸送する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.NonConnective
local instance sequentialTransportSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance sequentialTransportHomKan (X Y : OmegaSpectrum.{u}) :
    KanComplex (SimplicialCategory.sHom X Y) := OmegaSpectrum.mappingSpace_kanComplex X Y

/-- 同じ元の自然変換の各成分を持つ、サイズ調整した実際の prism。 -/
def sequentialDiagramPrism {D E : SpectrumSequence.{u}} (η : D ⟶ E) :
    (Δ[1] : SSet.{u + 1}) ⊗ (SSet.uliftFunctor.{u + 1, u}).obj (nerve SequentialIndex) ⟶
      SimplicialNerve OmegaSpectrum :=
  {
    app n := ↾fun z ↦ ((stdSimplex.objEquiv z.1).toOrderHom.toFunctor.prod' z.2.down) ⋙
      CategoryTheory.Functor.uncurry.obj (ComposableArrows.mk₁ η)
    naturality _ _ _ := by
      apply ConcreteCategory.hom_ext
      intro z
      apply CategoryTheory.Functor.ext (fun _ ↦ rfl) } ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent OmegaSpectrum

/-- prism の零端は元の始域図式に厳密に一致する。 -/
lemma sequentialDiagramPrism_zero {D E : SpectrumSequence.{u}} (η : D ⟶ E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ sequentialDiagramPrism η = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram D := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  apply congrArg ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent OmegaSpectrum).app n)
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- prism の一端は元の終域図式に厳密に一致する。 -/
lemma sequentialDiagramPrism_one {D E : SpectrumSequence.{u}} (η : D ⟶ E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ sequentialDiagramPrism η = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram E := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  apply congrArg ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent OmegaSpectrum).app n)
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- 同じ prism の垂直辺は、指定した元の成分の coherent 辺。 -/
lemma sequentialDiagramPrism_vertexEdge {D E : SpectrumSequence.{u}} (η : D ⟶ E)
    (a : SequentialIndex.{u}) :
    (sequentialDiagramPrism η).app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u + 1})),
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex a)) 1) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (η.app a)).edge := by
  apply congrArg ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent OmegaSpectrum).app (Opposite.op ⦋1⦌))
  apply ComposableArrows.ext₁
  case left => rfl
  case right => rfl
  case w =>
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    change η.app a ≫ E.map (𝟙 a) = η.app a
    rw [CategoryTheory.Functor.map_id, Category.comp_id]

/-- 全整数 π 同型な元の自然変換は、同じ coherent 図式間の実際の関手同型。 -/
def sequentialDiagramFunctorIso {D E : SpectrumSequence.{u}} (η : D ⟶ E)
    (hη : ∀ a, OmegaSpectrum.PiIsomorphism (η.app a)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram D) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram E) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.functorIsoOfPointwiseInvertibleHomotopy
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyOfPrism (sequentialDiagramPrism η)
      (sequentialDiagramPrism_zero η) (sequentialDiagramPrism_one η))
  rintro ⟨s⟩
  obtain ⟨a, rfl⟩ : ∃ a, s = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex a := ⟨s.obj 0, ComposableArrows.ext₀ rfl⟩
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
    ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyOfPrism_vertexEdge (sequentialDiagramPrism η)
      (sequentialDiagramPrism_zero η) (sequentialDiagramPrism_one η) _).trans
        (sequentialDiagramPrism_vertexEdge η a))).mpr
  exact OmegaSpectrum.isInvertible_of_piIsomorphism _ (hη a)

end SerrePositivity.KST.NonConnective
