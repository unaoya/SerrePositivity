module

public import SerrePositivity.KST.LocalizingInvariants.CompletionContractionPrism

/-!
概要：元の本質像の分母だけからなる wide 部分複体を、離散成分へ収縮する。
方針：周囲の全収縮の水平・垂直・斜辺を検査し、全単体を部分複体へ持ち上げる。
規約：元の wide 部分複体と両端を厳密に保持する。
使われ方：Sp-7 の Kan 置換後の正次数ホモトピー消滅への実入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable {C D : SSet.{u}} [Quasicategory C] [Quasicategory D] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable D]
  (f : C ⟶ D) [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor f] (h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f)

/-- 概要：選んだ全収縮の prism の全辺は、元の本質像の分母である。
方針：周囲の全収縮の水平・垂直・斜辺を検査し、全単体を部分複体へ持ち上げる。
規約：元の wide 部分複体と両端を厳密に保持する。
使われ方：Sp-7 の Kan 置換後の正次数ホモトピー消滅への実入力。 -/
lemma completionAmbientContraction_edges
    (s : ((completionCofiberWide f : SSet.{u}) ⊗ (Δ[1] : SSet.{u})) _⦋1⦌) :
    (completionAmbientContraction f h).h.app _ s ∈
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges (completionEssentialImage f) :=
  completionPrism_edges f h (completionAmbientContraction f h).h
    (completionAmbientContraction_horizontal f h)
    (completionAmbientContraction_vertical f h) s

/-- 概要：同じ全 prism の全単体が、元の全辺条件を満たす。
方針：周囲の全収縮の水平・垂直・斜辺を検査し、全単体を部分複体へ持ち上げる。
規約：元の wide 部分複体と両端を厳密に保持する。
使われ方：Sp-7 の Kan 置換後の正次数ホモトピー消滅への実入力。 -/
lemma completionAmbientContraction_range :
    Subcomplex.range (completionAmbientContraction f h).h ≤ completionCofiberWide f := by
  intro n s hs
  obtain ⟨t, rfl⟩ := hs
  intro θ
  have hh := (completionAmbientContraction f h).h.naturality_apply θ.op t
  exact Eq.mp (congrArg (fun d => d ∈
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges (completionEssentialImage f)) hh)
    (completionAmbientContraction_edges f h _)

/-- 概要：元の wide 部分複体内の全成分収縮を表す、一つの実 prism。
方針：周囲の全収縮の水平・垂直・斜辺を検査し、全単体を部分複体へ持ち上げる。
規約：元の wide 部分複体と両端を厳密に保持する。
使われ方：Sp-7 の Kan 置換後の正次数ホモトピー消滅への実入力。 -/
def completionWideContractionPrism :
    (completionCofiberWide f : SSet.{u}) ⊗ (Δ[1] : SSet.{u}) ⟶
      (completionCofiberWide f : SSet.{u}) :=
  Subcomplex.lift (completionAmbientContraction f h).h (completionAmbientContraction_range f h)

/-- 概要：離散成分への射とその切断の合成は、元の wide 内で恒等射にホモトピック。
方針：周囲の全収縮の水平・垂直・斜辺を検査し、全単体を部分複体へ持ち上げる。
規約：元の wide 部分複体と両端を厳密に保持する。
使われ方：Sp-7 の Kan 置換後の正次数ホモトピー消滅への実入力。 -/
def completionWideContraction : SSet.Homotopy (completionComponentCollapse f h)
    (𝟙 (completionCofiberWide f : SSet.{u})) where
  h := completionWideContractionPrism f h
  h₀ := by
    apply (cancel_mono (completionCofiberWide f).ι).1
    exact (completionAmbientContraction f h).h₀
  h₁ := by
    apply (cancel_mono (completionCofiberWide f).ι).1
    exact (completionAmbientContraction f h).h₁
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

end SerrePositivity.KST.LocalizingInvariants
