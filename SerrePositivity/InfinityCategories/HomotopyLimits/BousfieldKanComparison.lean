module

public import SerrePositivity.InfinityCategories.HomotopyLimits.WeightedExtensions
public import SerrePositivity.InfinityCategories.HomotopyLimits.ConeWeightAnodyne
public import SerrePositivity.InfinityCategories.HomotopyLimits.ConeWeightComparison

/-!
概要：anodyne な自然変換に沿う延長から実際の Bousfield–Kan 標準比較の同値性を得る。
方針：補助重みを経由し、点側と元の重み側の制限を全境界の持ち上げで比較する。
規約：入力の延長性は具体的な図式で証明し、∞ 極限性の主張とは区別する。
使われ方：Kerodon 7.5.3.12、7.5.4.6 の isofibrant な図式の標準比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {I : Type u} [SmallCategory I]

/-- 概要：成分ごとの anodyne な延長ができる図式の極限錐からの標準比較はホモトピー同値。
方針：一点重みの比較同型と二つの制限のホモトピー同値を組み合わせる。
規約：hH は延長の具体的な存在を要求する。極限錐の頂点の Kan 性は導出する。
使われ方：Kerodon 7.5.3.12、isofibrant な図式の strict 極限の比較。 -/
lemma bousfieldKanConeComparison_homotopyEquivalence_of_extensions
    {H : I ⥤ SSet.{u}} (c : Cone H) (hc : IsLimit c)
    (hH : ∀ {A B : I ⥤ SSet.{u}} (j : A ⟶ B),
      (∀ i, anodyneExtensions (j.app i)) → ∀ a : A ⟶ H, ∃ b : B ⟶ H, j ≫ b = a) :
    IsSimplicialHomotopyEquivalence (bousfieldKanConeComparison c) := by
  let U := (Functor.const I).obj (Δ[0] : SSet.{u})
  have hU : IsTerminal U := weightIsTerminalOfObj U (fun _ => stdSimplex.isTerminalObj₀)
  have := weightedConeComparison_isIso_of_isTerminalWeight U hU c hc
  have := weightedSections_kanComplex_of_extensions U H hH
  have := kanComplex_of_iso (asIso (weightedConeComparison U c)).symm
  have := weightedSections_kanComplex_of_extensions (bousfieldKanConeWeight I) H hH
  have : KanComplex (bousfieldKanHolim H) :=
    weightedSections_kanComplex_of_extensions (bousfieldKanWeight I) H hH
  have hV : IsSimplicialHomotopyEquivalence
      (weightedConeComparison (bousfieldKanConeWeight I) c) := by
    apply (weightedSectionsPre_homotopyEquivalence_of_extensions (H := H)
      bousfieldKanConeWeightPoint bousfieldKanConeWeightPoint_anodyne hH).cancel_right
    rw [bousfieldKanConeWeightComparison_point]
    exact homotopyEquivalence_of_isIso (weightedConeComparison U c)
  rw [← bousfieldKanConeComparison_factorization c]
  exact hV.comp (weightedSectionsPre_homotopyEquivalence_of_extensions (H := H)
    bousfieldKanConeWeightInclusion bousfieldKanConeWeightInclusion_anodyne hH)

/-- 概要：成分ごとの anodyne な延長ができる図式の実際の κ はホモトピー同値。
方針：選択された極限錐に標準比較の一般の定理を適用する。
規約：図式の圏のモデル構造の公理や弱同値の引用は使わない。
使われ方：Kerodon 7.5.3.12、7.5.4.6 の具体的な比較射。 -/
lemma bousfieldKanLimitComparison_homotopyEquivalence_of_extensions
    (H : I ⥤ SSet.{u})
    (hH : ∀ {A B : I ⥤ SSet.{u}} (j : A ⟶ B),
      (∀ i, anodyneExtensions (j.app i)) → ∀ a : A ⟶ H, ∃ b : B ⟶ H, j ≫ b = a) :
    IsSimplicialHomotopyEquivalence (bousfieldKanLimitComparison H) :=
  bousfieldKanConeComparison_homotopyEquivalence_of_extensions
    (limit.cone H) (limit.isLimit H) hH

end SerrePositivity.InfinityCategories.HomotopyLimits
