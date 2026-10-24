module

public import SerrePositivity.InfinityCategories.Core.InnerAnodyneEquivalence
public import SerrePositivity.InfinityCategories.Core.FunctorHomotopy

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
namespace SerrePositivity.InfinityCategories

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
  have : TrivialKanFibration p := trivialKanFibration_pre_of_innerAnodyne i hi X
  let b := functorVertex (i ≫ f)
  let v₀ : (vertexFiber p b) _⦋0⦌ := ⟨functorVertex f, by
    rw [pinchedConstant_zero]; rfl⟩
  let v₁ : (vertexFiber p b) _⦋0⦌ := ⟨functorVertex g, by
    rw [pinchedConstant_zero]
    change functorVertex (i ≫ g) = functorVertex (i ≫ f)
    rw [h]⟩
  have hc := vertexFiber_isContractibleKan p b
  obtain ⟨k⟩ := (hc.isInitialVertex v₀).nonempty_edge v₁
  let k' := k.map ((truncation 2).map (vertexFiberι p b))
  have hk : p.app (Opposite.op ⦋1⦌) k'.edge =
      (SSet.Truncated.Edge.id (X := (truncation 2).obj ((ihom A).obj X)) b).edge := by
    change (vertexFiberι p b ≫ p).app (Opposite.op ⦋1⦌) k.edge = _
    rw [vertexFiberι_comp]
    rfl
  refine ⟨simplicialHomotopyOfFunctorEdge k', ?_⟩
  change (i ▷ (Δ[1] : SSet.{u})) ≫ uncurry (SSet.yonedaEquiv.symm k'.edge) = _
  rw [← uncurry_pre_app, SSet.yonedaEquiv_symm_comp]
  change uncurry (SSet.yonedaEquiv.symm (p.app (Opposite.op ⦋1⦌) k'.edge)) = _
  rw [hk]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨x, t⟩
  rfl

end SerrePositivity.InfinityCategories
