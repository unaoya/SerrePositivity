module

public import SerrePositivity.KST.NonConnective.SequentialDiagramTransport
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.SquareFunctorTransport

/-!
概要：同じ BF 余錐全体の比較を行うための、サイズを調整した自然変換の実現。
方針：実際の通常の prism の各成分を保持し、点ごとの可逆性で関手同型を作る。
規約：一般の安定圏上の K の構成ではなく、元の BF 錐の輸送用の形式的補題。
使われ方：相対置換列から元の段ごとの実余錐への余極限性の移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.NonConnective
variable {I : Type (max u v)} [SmallCategory I]
  {C : Type v} [Category.{u} C] [SimplicialCategory C]

/-- 元の比較自然変換を、対象と Hom の宇宙を分離した prism として実現する。 -/
def sequentialResizedPrism {F G : I ⥤ C} (η : F ⟶ G) :
    (Δ[1] : SSet.{max u v}) ⊗ nerve I ⟶ SimplicialNerve C :=
  {
    app n := ↾fun z ↦ ((stdSimplex.objEquiv z.1).toOrderHom.toFunctor.prod' z.2) ⋙
      CategoryTheory.Functor.uncurry.obj (ComposableArrows.mk₁ η)
    naturality _ _ _ := by
      apply ConcreteCategory.hom_ext
      intro z
      apply CategoryTheory.Functor.ext (fun _ ↦ rfl) } ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent C

/-- prism の零端は元の始域関手。 -/
lemma sequentialResizedPrism_zero {F G : I ⥤ C} (η : F ⟶ G) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ sequentialResizedPrism η = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.resizedNerveMap F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent C := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  apply congrArg ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent C).app n)
  apply CategoryTheory.Functor.ext
  case h_obj => intro i; rfl
  case h_map =>
    intro i j f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    change 𝟙 _ ≫ F.map (s.map _) = F.map (s.map _)
    exact Category.id_comp _

/-- prism の一端は元の終域関手。 -/
lemma sequentialResizedPrism_one {F G : I ⥤ C} (η : F ⟶ G) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ sequentialResizedPrism η = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.resizedNerveMap G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent C := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  apply congrArg ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent C).app n)
  apply CategoryTheory.Functor.ext
  case h_obj => intro i; rfl
  case h_map =>
    intro i j f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    change 𝟙 _ ≫ G.map (s.map _) = G.map (s.map _)
    exact Category.id_comp _

/-- 同じ prism の垂直辺は、元の指定成分の coherent 辺。 -/
lemma sequentialResizedPrism_vertexEdge {F G : I ⥤ C} (η : F ⟶ G) (a : I) :
    (sequentialResizedPrism η).app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{max u v})),
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex a) 1) = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (η.app a)).edge := by
  apply congrArg ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent C).app (Opposite.op ⦋1⦌))
  apply ComposableArrows.ext₁
  case left => rfl
  case right => rfl
  case w =>
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    change η.app a ≫ G.map (𝟙 a) = η.app a
    rw [CategoryTheory.Functor.map_id, Category.comp_id]

/-- 可逆な指定成分を持つ通常の比較から、同じ resized 図式間の関手同型を作る。 -/
def sequentialResizedFunctorIso [∀ X Y : C, KanComplex (SimplicialCategory.sHom X Y)]
    {F G : I ⥤ C} (η : F ⟶ G)
    (hη : ∀ a, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (η.app a))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.resizedNerveMap F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent C)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.resizedNerveMap G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent C) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.functorIsoOfPointwiseInvertibleHomotopy
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyOfPrism (sequentialResizedPrism η)
      (sequentialResizedPrism_zero η) (sequentialResizedPrism_one η))
  intro s
  obtain ⟨a, rfl⟩ : ∃ a, s = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex a := ⟨s.obj 0, ComposableArrows.ext₀ rfl⟩
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
    ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyOfPrism_vertexEdge (sequentialResizedPrism η)
      (sequentialResizedPrism_zero η) (sequentialResizedPrism_one η) _).trans
        (sequentialResizedPrism_vertexEdge η a))).mpr (hη a)

end SerrePositivity.KST.NonConnective
