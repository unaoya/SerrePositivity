module

public meta import SerrePositivity.Util.Citation

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.JointRealizationComposition
/-!
概要：指定された任意の合成比較を、元の全図式比較の実現の合成として読む。
方針：既存jointRealizationIso_transを使い、比較の成分の等式でχを同じ合成に同定する。
規約：HTT §1.1.5、Kerodon §3.1（Tag 00SZ）のcoherent実現に関する構成の法則。
  全添字・全係数の族の合成を、点ごとの同型を集めずに保持する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
/-- 元の二つの全図式比較の実現の合成は、同じ成分を持つ指定比較χの実現に一致する。
HTT §1.1.5に対応するKan値のcoherent実現の合成則への特殊化。
既存の全joint族の三角形による合成定理をそのまま再利用する。 -/
@[cite HTT "1.1.5" (partial := special)
  "Kan値豊穣図式の全joint比較の実現に関する、指定合成との照合法則。"]
lemma kanEnrichedDiagramRealizationIso_trans
    {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J] {D E F : KanEnrichedDiagram C J}
    (η : KanEnrichedDiagramComparison D E) (θ : KanEnrichedDiagramComparison E F)
    (χ : KanEnrichedDiagramComparison D F)
    (hχ : ∀ j, χ.component j = KanEnrichedComparison.trans (η.component j) (θ.component j))
    (hη : ∀ j (X : C), IsQCatEquivalence ((η.component j).val X))
    (hθ : ∀ j (X : C), IsQCatEquivalence ((θ.component j).val X))
    (hχe : ∀ j (X : C), IsQCatEquivalence ((χ.component j).val X)) :
    η.realizationIso hη ≪≫ θ.realizationIso hθ = χ.realizationIso hχe := by
  have hc : χ = jointComparisonTrans η θ := by
    cases χ with
    | mk c h =>
      have he : c = (jointComparisonTrans η θ).component := funext hχ
      cases he
      rfl
  subst χ
  exact jointRealizationIso_trans η θ hη hθ hχe
end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
