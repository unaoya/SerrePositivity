module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.DiagramCommaSmallness
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FullSubcomplexIso

/-!
概要：固定頂点写像が小さい ∞ 圏の、小さい頂点集合上の全部分圏は各次数で小さい。
方針：単体を頂点族と同じ全 Yoneda 写像の組へ単射で符号化する。
規約：同値類の個数ではなく、元の全部分複体の全単体の小ささを証明する。
使われ方：Ind 内の共通の小さい compact 生成族を、小さい全部分生成圏へ戻す。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 頂点と固定頂点の全写像が小さければ、元の各次数の単体そのものが小さい。 -/
lemma small_simplices_of_smallFixedVertexMaps {X : SSet.{u + 1}}
    (hX : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasSmallFixedVertexMaps X) [Small.{u} (X _⦋0⦌)]
    (n : SimplexCategoryᵒᵖ) : Small.{u} (X.obj n) := by
  rcases n with ⟨⟨n⟩⟩
  have hΔ (m : SimplexCategoryᵒᵖ) : Small.{u} ((Δ[n] : SSet.{u + 1}).obj m) :=
    inferInstance
  let T (v : (Δ[n] : SSet.{u + 1}) _⦋0⦌ → X _⦋0⦌) :=
    {f : (Δ[n] : SSet.{u + 1}) ⟶ X // ∀ a, f.app _ a = v a}
  have (v : (Δ[n] : SSet.{u + 1}) _⦋0⦌ → X _⦋0⦌) : Small.{u} (T v) := hX Δ[n] hΔ v
  let code (s : X _⦋n⦌) : Σ v, T v :=
    ⟨(SSet.yonedaEquiv.symm s).app _, ⟨SSet.yonedaEquiv.symm s, fun _ ↦ rfl⟩⟩
  apply small_of_injective (f := code)
  intro s t h
  apply SSet.yonedaEquiv.symm.injective
  exact congrArg (fun z : Σ v, T v ↦ z.2.val) h

/-- 小さい族の値に頂点を制限した元の全部分複体は、全次数で小さい。 -/
lemma small_fullSubcomplexOnRange {X : SSet.{u + 1}}
    (hX : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasSmallFixedVertexMaps X) {T : Type u} (v : T → X _⦋0⦌)
    (n : SimplexCategoryᵒᵖ) :
    Small.{u} ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X (fun x ↦ x ∈ Set.range v)).toSSet.obj n) := by
  let Y := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X (fun x ↦ x ∈ Set.range v)
  have hv : Small.{u} (Y.toSSet _⦋0⦌) := by
    let f (x : Y.toSSet _⦋0⦌) : Set.range v := ⟨x.val, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex x⟩
    apply small_of_injective (f := f)
    intro x y h
    exact Subtype.ext (congrArg (fun z : Set.range v ↦ z.val) h)
  have hm : Mono Y.ι := inferInstance
  exact small_simplices_of_smallFixedVertexMaps (hX.of_mono Y.ι) n

/-- 元の Ind 圏の任意の小さい頂点族上の全部分圏は、実際に全次数で小さい。 -/
lemma ind_small_fullSubcomplexOnRange (κ : Cardinal.{u}) (A : SSet.{u}) [Quasicategory A]
    {T : Type u} (v : T → (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ A) _⦋0⦌) (n : SimplexCategoryᵒᵖ) :
    Small.{u} ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ A)
      (fun x ↦ x ∈ Set.range v)).toSSet.obj n) :=
  small_fullSubcomplexOnRange (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ind_hasSmallFixedVertexMaps κ A) v n

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
