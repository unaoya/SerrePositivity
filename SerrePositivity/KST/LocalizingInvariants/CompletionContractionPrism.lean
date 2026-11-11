module

public import SerrePositivity.KST.LocalizingInvariants.CompletionComponentContraction

/-!
概要：選んだ成分収縮の水平辺と垂直辺を、元の分母として照合する。
方針：水平辺は厳密な二端点へ、垂直辺は標準区間の三自己射へ帰着する。
規約：全区間の全辺を検査し、零射の点ごとの存在だけで代用しない。
使われ方：全 prism を元の wide 部分複体へ持ち上げる。
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
include h

/-- 概要：元の全図式収縮の水平辺は、始点と終点の元の wide 辺である。
方針：水平辺は厳密な二端点へ、垂直辺は標準区間の三自己射へ帰着する。
規約：全区間の全辺を検査し、零射の点ごとの存在だけで代用しない。
使われ方：全 prism を元の wide 部分複体へ持ち上げる。 -/
lemma completionAmbientContraction_horizontal
    (e : (completionCofiberWide f : SSet.{u}) _⦋1⦌)
    (t : (Δ[1] : SSet.{u}) _⦋0⦌) :
    (completionAmbientContraction f h).h.app _ (e, (Δ[1] : SSet.{u}).σ 0 t) ∈
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges (completionEssentialImage f) := by
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective t
  fin_cases i
  · have hh := congrArg (fun l => l.app (Opposite.op ⦋1⦌) e)
      (completionAmbientContraction f h).h₀
    change (completionAmbientContraction f h).h.app _
      (e, (Δ[1] : SSet.{u}).σ 0 (stdSimplex.obj₀Equiv.symm 0)) =
        ((completionComponentCollapse f h).app _ e).val at hh
    exact hh.symm ▸ (by
      simpa using ((completionComponentCollapse f h).app _ e).property (𝟙 ⦋1⦌))
  · have hh := congrArg (fun l => l.app (Opposite.op ⦋1⦌) e)
      (completionAmbientContraction f h).h₁
    change (completionAmbientContraction f h).h.app _
      (e, (Δ[1] : SSet.{u}).σ 0 (stdSimplex.obj₀Equiv.symm 1)) = e.val at hh
    exact hh.symm ▸ (by simpa using e.property (𝟙 ⦋1⦌))

/-- 概要：同じ全収縮の全ての垂直辺は、元の零分母またはその端点の退化辺。
方針：水平辺は厳密な二端点へ、垂直辺は標準区間の三自己射へ帰着する。
規約：全区間の全辺を検査し、零射の点ごとの存在だけで代用しない。
使われ方：全 prism を元の wide 部分複体へ持ち上げる。 -/
lemma completionAmbientContraction_vertical
    (x : (completionCofiberWide f : SSet.{u}) _⦋0⦌)
    (a : (Δ[1] : SSet.{u}) _⦋1⦌) :
    (completionAmbientContraction f h).h.app _
      ((completionCofiberWide f : SSet.{u}).σ 0 x, a) ∈
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges (completionEssentialImage f) := by
  obtain ⟨θ, rfl⟩ := (stdSimplex.objEquiv
    (n := ⦋1⦌) (m := Opposite.op ⦋1⦌)).symm.surjective a
  rcases _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.intervalEndomorphism_cases θ with ht | ht | ht
  · subst θ
    change (completionAmbientContraction f h).h.app _
      (((completionCofiberWide f : SSet.{u})).σ 0 x,
        (Δ[1] : SSet.{u}).σ 0 (stdSimplex.obj₀Equiv.symm 0)) ∈ _
    have hh := (completionAmbientContraction f h).h.naturality_apply
      (SimplexCategory.σ (0 : Fin 1)).op
      ((x, stdSimplex.obj₀Equiv.symm (0 : Fin 2)) :
        ((completionCofiberWide f : SSet.{u}) ⊗ (Δ[1] : SSet.{u})) _⦋0⦌)
    exact hh.symm ▸ completionCofiber_degenerate f h _
  · subst θ
    convert completionAmbientContraction_component f h x using 1
    congr 1
    apply congrArg
    apply SSet.stdSimplex.objEquiv.injective
    apply SimplexCategory.Hom.ext
    apply DFunLike.ext
    intro i
    fin_cases i <;> rfl
  · subst θ
    change (completionAmbientContraction f h).h.app _
      (((completionCofiberWide f : SSet.{u})).σ 0 x,
        (Δ[1] : SSet.{u}).σ 0 (stdSimplex.obj₀Equiv.symm 1)) ∈ _
    have hh := (completionAmbientContraction f h).h.naturality_apply
      (SimplexCategory.σ (0 : Fin 1)).op
      ((x, stdSimplex.obj₀Equiv.symm (1 : Fin 2)) :
        ((completionCofiberWide f : SSet.{u}) ⊗ (Δ[1] : SSet.{u})) _⦋0⦌)
    exact hh.symm ▸ completionCofiber_degenerate f h _

end SerrePositivity.KST.LocalizingInvariants
