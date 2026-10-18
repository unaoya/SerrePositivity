module

public import SerrePositivity.InfinityCategories.F1.StrictDiagramRestrictionFibration
public import SerrePositivity.InfinityCategories.F1.StrictDiagramMappingVertices
public import SerrePositivity.InfinityCategories.F1.RelativeFunctorExtensionSpace

/-!
概要：strict transport への比較を部分図式上で厳密に固定した延長の選択空間。
方針：変換空間の制限の fiber を取り、単射な同値の場合の全境界持ち上げを使う。
規約：これは strict な図式間の延長であり、一般の coherent 図式の分類は含めない。
使われ方：Kerodon §§5.6.5–5.6.8、固定した比較を保つ高次の延長と選択の一意性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：通常の自然変換の strict な変換空間の頂点表示は単射。
方針：対象ごとの内部 Hom の頂点表示の単射性を使う。
規約：係数図式に Kan 性を要求しない。
使われ方：Kerodon §5.3.1、延長空間の頂点の等式を自然変換の等式へ戻す。 -/
lemma strictDiagramMappingVertex_injective {C : Type u} [Category.{u} C]
    (F G : C ⥤ SSet.{u}) :
    Function.Injective (strictDiagramMappingVertex (F := F) (G := G)) := by
  intro η θ h
  apply NatTrans.ext
  funext c
  apply functorVertex_injective
  exact congrArg (fun s : (strictDiagramMappingSpace F G) _⦋0⦌ ↦ s.val c) h

/-- 概要：部分図式上の比較 θ を厳密に延長する strict な比較の空間。
方針：前合成による変換空間の制限の θ の頂点上の fiber を取る。
規約：η・q・θ の充填性は空間の定義には不要。
使われ方：Kerodon Corollary 5.6.5.15、固定した比較の延長の高次の選択空間。 -/
def strictDiagramExtensionSpace {C : Type u} [Category.{u} C]
    {F G : C ⥤ SSet.{u}} (η : F ⟶ G) {E : SSet.{u}} (q : E ⟶ nerve C)
    (θ : F ⟶ leftStrictTransportDiagram q) : SSet.{u} :=
  vertexFiber (strictDiagramMappingPre η (leftStrictTransportDiagram q))
    (strictDiagramMappingVertex θ)

/-- 概要：単射な対象ごとの同値を越える strict な比較の延長の空間は可縮な Kan 複体。
方針：制限の全境界持ち上げから、その各 fiber の可縮性を得る。
規約：両係数図式は Kan 値、q は left fibration。
使われ方：Kerodon §§5.6.5–5.6.8、延長の存在と全ての高次の選択の一意性。 -/
lemma strictDiagramExtensionSpace_isContractibleKan {C : Type u} [Category.{u} C]
    {F G : C ⥤ SSet.{u}} [∀ c, KanComplex (F.obj c)] [∀ c, KanComplex (G.obj c)]
    (η : F ⟶ G) [∀ c, Mono (η.app c)] (hη : ∀ c, IsQCatEquivalence (η.app c))
    {E : SSet.{u}} (q : E ⟶ nerve C) [LeftFibration q]
    (θ : F ⟶ leftStrictTransportDiagram q) :
    IsContractibleKan (strictDiagramExtensionSpace η q θ) := by
  have := strictDiagramMappingPre_trivialKanFibration η hη q
  exact vertexFiber_isContractibleKan _ _

/-- 概要：対象ごとに単射な同値を越えて、strict transport への比較を厳密に延長できる。
方針：可縮な延長空間の頂点を取り、通常の自然変換へ戻す。
規約：η≫Θ=θ は厳密な自然変換の等式。
使われ方：Kerodon §5.6.5、既存の部分比較を保ったまま図式の解像を変更する。 -/
lemma exists_strictDiagramExtension {C : Type u} [Category.{u} C]
    {F G : C ⥤ SSet.{u}} [∀ c, KanComplex (F.obj c)] [∀ c, KanComplex (G.obj c)]
    (η : F ⟶ G) [∀ c, Mono (η.app c)] (hη : ∀ c, IsQCatEquivalence (η.app c))
    {E : SSet.{u}} (q : E ⟶ nerve C) [LeftFibration q]
    (θ : F ⟶ leftStrictTransportDiagram q) :
    ∃ Θ : G ⟶ leftStrictTransportDiagram q, η ≫ Θ = θ := by
  obtain ⟨x⟩ := (strictDiagramExtensionSpace_isContractibleKan η hη q θ).nonempty
  obtain ⟨Θ, hΘ⟩ := exists_strictDiagramMappingVertex G (leftStrictTransportDiagram q) x.val
  refine ⟨Θ, strictDiagramMappingVertex_injective F (leftStrictTransportDiagram q) ?_⟩
  have hx := x.property
  change (strictDiagramMappingPre η (leftStrictTransportDiagram q)).app _ x.val =
    strictDiagramMappingVertex θ at hx
  rw [← hΘ, strictDiagramMappingPre_vertex] at hx
  exact hx

end SerrePositivity.InfinityCategories
