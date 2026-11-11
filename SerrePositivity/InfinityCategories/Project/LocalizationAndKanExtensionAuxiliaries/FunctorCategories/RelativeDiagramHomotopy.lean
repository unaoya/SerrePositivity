module

public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.InnerAnodyneEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorHomotopy

/-!
概要：inner anodyne な部分図式を固定した延長の比較。
方針：制限写像の可縮な fiber 内の辺を実際のホモトピーに展開する。
規約：制限後のホモトピーが定値となることを射の等式で保持する。
使われ方：B1 の合成三角形の比較で二辺の coherence を固定する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories

/-- 概要：inner anodyne な部分図式上で一致する二つの延長は相対ホモトピック。
方針：前合成の trivial Kan fibration の fiber の二頂点を辺で結ぶ。
規約：部分図式の上ではホモトピーそのものが時間によらず一定。
使われ方：指定二辺を変えない合成三角形の輸送。 -/
lemma exists_homotopy_relative_innerAnodyne {A B X : SSet.{u}} [Quasicategory X]
    (i : A ⟶ B) (hi : innerAnodyneExtensions i) (f g : B ⟶ X)
    (h : i ≫ g = i ≫ f) :
    ∃ H : SSet.Homotopy f g,
      (i ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst A (Δ[1] : SSet.{u}) ≫ i ≫ f := by
  let p := (pre i).app X
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.trivialKanFibration_pre_of_innerAnodyne i hi X
  let b := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (i ≫ f)
  let v₀ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) _⦋0⦌ := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f, by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]; rfl⟩
  let v₁ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) _⦋0⦌ := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g, by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (i ≫ g) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (i ≫ f)
    rw [h]⟩
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_isContractibleKan p b
  obtain ⟨k⟩ := (hc.isInitialVertex v₀).nonempty_edge v₁
  let k' := k.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b))
  have hk : p.app (Opposite.op ⦋1⦌) k'.edge =
      (SSet.Truncated.Edge.id (X := (truncation 2).obj ((ihom A).obj X)) b).edge := by
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b ≫ p).app (Opposite.op ⦋1⦌) k.edge = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp]
    rfl
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge k', ?_⟩
  change (i ▷ (Δ[1] : SSet.{u})) ≫ uncurry (SSet.yonedaEquiv.symm k'.edge) = _
  rw [← uncurry_pre_app, SSet.yonedaEquiv_symm_comp]
  change uncurry (SSet.yonedaEquiv.symm (p.app (Opposite.op ⦋1⦌) k'.edge)) = _
  rw [hk]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨x, t⟩
  rfl

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
