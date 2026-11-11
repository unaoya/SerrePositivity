module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.YonedaInfinityConstruction
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FilteredInfinity

/-!
概要：前層内の Yoneda 像の、同型と小さい κ-filtered 余極限による最小閉包を構成する。
方針：同じ元の頂点条件を満たす全閉包の交差を命題として取る。
規約：κ-filtered 性は F2N-1 の既存定義を使う。生成・普遍性は定義に仮定しない。
使われ方：F2N-2(b) の全部分 ∞ 圏の頂点条件。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- 元の頂点条件が、前層 ∞ 圏内の同型で閉じていること。 -/
def IsIsoClosed {X : SSet.{u + 1}} (P : X _⦋0⦌ → Prop) : Prop :=
  ∀ {x y}, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso x y → P x → P y

/-- 元の頂点条件が、元の前層圏内の小さい κ-filtered な native 余極限で閉じていること。 -/
def IsKappaColimitClosed (κ : Cardinal.{u}) {X : SSet.{u + 1}} (P : X _⦋0⦌ → Prop) : Prop :=
  ∀ (I : SSet.{u}) [Quasicategory I] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ I]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ X) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D),
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c → (∀ i : I _⦋0⦌, P (D.app (Opposite.op ⦋0⦌) (ULift.up i))) → P c.vertex

/-- 同じ Yoneda 像を含み同型と小さい κ-filtered 余極限で閉じた最小の前層頂点条件。 -/
def IsIndVertex (κ : Cardinal.{u}) (C : SSet.{u}) [Quasicategory C]
    (F : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C) _⦋0⦌) : Prop :=
  ∀ P : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C) _⦋0⦌ → Prop,
    (∀ x : C _⦋0⦌, P ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C).app (Opposite.op ⦋0⦌) (ULift.up x))) →
    IsIsoClosed P → IsKappaColimitClosed κ P → P F

/-- 元の Yoneda の各対象は、同じ最小閉包に属する。 -/
lemma isIndVertex_yoneda (κ : Cardinal.{u}) {C : SSet.{u}} [Quasicategory C] (x : C _⦋0⦌) :
    IsIndVertex κ C ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C).app (Opposite.op ⦋0⦌) (ULift.up x)) :=
  fun _ h _ _ ↦ h x

/-- 同じ元の最小閉包は、前層内の指定同型で閉じている。 -/
lemma isIndVertex_isoClosed (κ : Cardinal.{u}) (C : SSet.{u}) [Quasicategory C] :
    IsIsoClosed (IsIndVertex κ C) := by
  intro x y e hx P hP hIso hColim
  exact hIso e (hx P hP hIso hColim)

/-- 同じ元の最小閉包は、小さい κ-filtered 余極限で閉じている。 -/
lemma isIndVertex_kappaColimitClosed (κ : Cardinal.{u}) (C : SSet.{u}) [Quasicategory C] :
    IsKappaColimitClosed κ (IsIndVertex κ C) := by
  intro I hI hFiltered D c hc hD P hP hIso hColim
  exact hColim I D c hc (fun i ↦ hD i P hP hIso hColim)

/-- 同じ閉性を持つ任意の頂点条件は、この最小閉包を含む。関手の延長の普遍性とは区別する。 -/
lemma isIndVertex_minimal (κ : Cardinal.{u}) {C : SSet.{u}} [Quasicategory C]
    (P : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C) _⦋0⦌ → Prop)
    (hP : ∀ x : C _⦋0⦌, P ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C).app (Opposite.op ⦋0⦌) (ULift.up x)))
    (hIso : IsIsoClosed P) (hColim : IsKappaColimitClosed κ P)
    {F : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C) _⦋0⦌} (hF : IsIndVertex κ C F) : P F :=
  hF P hP hIso hColim

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
