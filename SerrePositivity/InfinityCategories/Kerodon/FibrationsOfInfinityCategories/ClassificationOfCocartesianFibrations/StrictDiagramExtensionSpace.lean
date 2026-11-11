module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.StrictDiagramRestrictionFibration
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.StrictDiagramMappingVertices
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.RelativeFunctorExtensionSpace

/-!
概要：strict transport への比較を部分図式上で厳密に固定した延長の選択空間。
方針：変換空間の制限の fiber を取り、単射な同値の場合の全境界持ち上げを使う。
規約：これは strict な図式間の延長であり、一般の coherent 図式の分類は含めない。
使われ方：Kerodon §§5.6.5（Tag 028U）–5.6.8（Tag 02S9）、固定した比較を保つ高次の延長と選択の一意性。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：通常の自然変換の strict な変換空間の頂点表示は単射。
方針：対象ごとの内部 Hom の頂点表示の単射性を使う。
規約：係数図式に Kan 性を要求しない。
使われ方：Kerodon §5.3.1（Tag 035D）、延長空間の頂点の等式を自然変換の等式へ戻す。 -/
lemma strictDiagramMappingVertex_injective {C : Type u} [Category.{u} C]
    (F G : C ⥤ SSet.{u}) :
    Function.Injective (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMappingVertex (F := F) (G := G)) := by
  intro η θ h
  apply NatTrans.ext
  funext c
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_injective
  exact congrArg (fun s : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSpace F G) _⦋0⦌ ↦ s.val c) h

/-- 概要：部分図式上の比較 θ を厳密に延長する strict な比較の空間。
方針：前合成による変換空間の制限の θ の頂点上の fiber を取る。
規約：η・q・θ の充填性は空間の定義には不要。
使われ方：Kerodon Corollary 5.6.5.15（Tag 0296）、固定した比較の延長の高次の選択空間。 -/
def strictDiagramExtensionSpace {C : Type u} [Category.{u} C]
    {F G : C ⥤ SSet.{u}} (η : F ⟶ G) {E : SSet.{u}} (q : E ⟶ nerve C)
    (θ : F ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram q) : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMappingPre η (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram q))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMappingVertex θ)

/-- 概要：単射な対象ごとの同値を越える strict な比較の延長の空間は可縮な Kan 複体。
方針：制限の全境界持ち上げから、その各 fiber の可縮性を得る。
規約：両係数図式は Kan 値、q は left fibration。
使われ方：Kerodon §§5.6.5（Tag 028U）–5.6.8（Tag 02S9）、延長の存在と全ての高次の選択の一意性。 -/
lemma strictDiagramExtensionSpace_isContractibleKan {C : Type u} [Category.{u} C]
    {F G : C ⥤ SSet.{u}} [∀ c, KanComplex (F.obj c)] [∀ c, KanComplex (G.obj c)]
    (η : F ⟶ G) [∀ c, Mono (η.app c)] (hη : ∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (η.app c))
    {E : SSet.{u}} (q : E ⟶ nerve C) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q]
    (θ : F ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram q) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (strictDiagramExtensionSpace η q θ) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMappingPre_trivialKanFibration η hη q
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_isContractibleKan _ _

/-- 概要：対象ごとに単射な同値を越えて、strict transport への比較を厳密に延長できる。
方針：可縮な延長空間の頂点を取り、通常の自然変換へ戻す。
規約：η≫Θ=θ は厳密な自然変換の等式。
使われ方：Kerodon §5.6.5（Tag 028U）、既存の部分比較を保ったまま図式の解像を変更する。 -/
lemma exists_strictDiagramExtension {C : Type u} [Category.{u} C]
    {F G : C ⥤ SSet.{u}} [∀ c, KanComplex (F.obj c)] [∀ c, KanComplex (G.obj c)]
    (η : F ⟶ G) [∀ c, Mono (η.app c)] (hη : ∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (η.app c))
    {E : SSet.{u}} (q : E ⟶ nerve C) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q]
    (θ : F ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram q) :
    ∃ Θ : G ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram q, η ≫ Θ = θ := by
  obtain ⟨x⟩ := (strictDiagramExtensionSpace_isContractibleKan η hη q θ).nonempty
  obtain ⟨Θ, hΘ⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.exists_strictDiagramMappingVertex G (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram q) x.val
  refine ⟨Θ, strictDiagramMappingVertex_injective F (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram q) ?_⟩
  have hx := x.property
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMappingPre η (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram q)).app _ x.val =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMappingVertex θ at hx
  rw [← hΘ, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMappingPre_vertex] at hx
  exact hx

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
