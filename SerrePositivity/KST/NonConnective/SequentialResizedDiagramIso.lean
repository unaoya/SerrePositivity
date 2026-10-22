module

public import SerrePositivity.KST.NonConnective.SequentialDiagramTransport
public import SerrePositivity.InfinityCategories.Stable.SquareFunctorTransport

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
open SerrePositivity.InfinityCategories SerrePositivity.InfinityCategories.HomotopyLimits
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
      apply CategoryTheory.Functor.ext (fun _ ↦ rfl) } ≫ nerveToCoherent C

/-- prism の零端は元の始域関手。 -/
lemma sequentialResizedPrism_zero {F G : I ⥤ C} (η : F ⟶ G) :
    prismEndpoint 0 _ ≫ sequentialResizedPrism η = resizedNerveMap F ≫ nerveToCoherent C := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  apply congrArg ((nerveToCoherent C).app n)
  apply CategoryTheory.Functor.ext
  case h_obj => intro i; rfl
  case h_map =>
    intro i j f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    change 𝟙 _ ≫ F.map (s.map _) = F.map (s.map _)
    exact Category.id_comp _

/-- prism の一端は元の終域関手。 -/
lemma sequentialResizedPrism_one {F G : I ⥤ C} (η : F ⟶ G) :
    prismEndpoint 1 _ ≫ sequentialResizedPrism η = resizedNerveMap G ≫ nerveToCoherent C := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  apply congrArg ((nerveToCoherent C).app n)
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
        PinchedHom.constant (nerveVertex a) 1) = (coherentNerveEdge (η.app a)).edge := by
  apply congrArg ((nerveToCoherent C).app (Opposite.op ⦋1⦌))
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
    (hη : ∀ a, IsInvertibleEdge (coherentNerveEdge (η.app a))) :
    FunctorIso (resizedNerveMap F ≫ nerveToCoherent C)
      (resizedNerveMap G ≫ nerveToCoherent C) := by
  apply functorIsoOfPointwiseInvertibleHomotopy
    (homotopyOfPrism (sequentialResizedPrism η)
      (sequentialResizedPrism_zero η) (sequentialResizedPrism_one η))
  intro s
  obtain ⟨a, rfl⟩ : ∃ a, s = nerveVertex a := ⟨s.obj 0, ComposableArrows.ext₀ rfl⟩
  exact (isInvertibleEdge_congr
    ((homotopyOfPrism_vertexEdge (sequentialResizedPrism η)
      (sequentialResizedPrism_zero η) (sequentialResizedPrism_one η) _).trans
        (sequentialResizedPrism_vertexEdge η a))).mpr (hη a)

end SerrePositivity.KST.NonConnective
