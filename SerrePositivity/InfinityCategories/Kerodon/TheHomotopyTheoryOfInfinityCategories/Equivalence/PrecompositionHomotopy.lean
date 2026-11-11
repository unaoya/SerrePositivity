module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrecompositionEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalenceTwoOfSix
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：前合成の同値条件の二対六則と可逆ホモトピーによる不変性。
方針：任意の quasicategory への前合成に既存の同値の計算を適用する。
規約：元の単体集合は quasicategory でなくてもよい。
使われ方：Kerodon §4.6.2（Tag 01HM） の fat join の標準単体の変形。

対応節は Kerodon 4.5（Tag 01DE）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

/-- 概要：隣接する二つの合成の同値条件から中央の射の同値条件が従う。
方針：前合成の逆順の合成に同値の二対六則を使う。
規約：四つの元の単体集合の quasicategory 性は不要。
使われ方：Kerodon §4.6.2（Tag 01HM） の比較射の検出。 -/
lemma isPrecompositionEquivalence_of_composites {A B C D : SSet.{u}}
    {f : A ⟶ B} {g : B ⟶ C} {h : C ⟶ D}
    (hfg : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (f ≫ g))
    (hgh : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (g ≫ h)) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence g := by
  intro X hX
  have h₀ := hfg X
  have h₁ := hgh X
  rw [pre_map, NatTrans.comp_app] at h₀ h₁
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_composites h₁ h₀

/-- 概要：点ごとに可逆なホモトピーで結ばれた射の前合成の同値条件は同値。
方針：各標的の関手単体集合で前合成の二つの射を同型にする。
規約：元の二つの単体集合の quasicategory 性は不要。
使われ方：Kerodon §4.6.2（Tag 01HM） の標準単体の変形。 -/
@[kerodon 033Z]
lemma isPrecompositionEquivalence_iff_of_homotopy {A B : SSet.{u}} {f g : A ⟶ B}
    (H : SSet.Homotopy f g)
    (hH : ∀ a : A _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H a).toTruncated) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence f ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence g := by
  constructor
  · intro hf X hX
    exact (hf X).ofFunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.functorIsoPrecompositionOfHomotopy H hH X)
  · intro hg X hX
    exact (hg X).ofFunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.functorIsoPrecompositionOfHomotopy H hH X).symm

/-- 概要：切断と二つの可逆ホモトピーによる変形は前合成の同値条件を与える。
方針：一方の合成の恒等式と他方の合成のホモトピーによる不変性を二対六則で合わせる。
規約：二つのホモトピーの向きを反転することは要求しない。
使われ方：Kerodon Theorem 4.6.2.8（Tag 01HV） の標準単体の fat join の変形。 -/
lemma isPrecompositionEquivalence_of_section_zigzag {A B : SSet.{u}}
    (f : A ⟶ B) (g : B ⟶ A) (hgf : g ≫ f = 𝟙 B) (r : A ⟶ A)
    (H₀ : SSet.Homotopy (𝟙 A) r) (H₁ : SSet.Homotopy (f ≫ g) r)
    (h₀ : ∀ a : A _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H₀ a).toTruncated)
    (h₁ : ∀ a : A _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H₁ a).toTruncated) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence f := by
  apply isPrecompositionEquivalence_of_composites (f := g) (h := g)
  · rw [hgf]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_id _
  · exact (isPrecompositionEquivalence_iff_of_homotopy H₁ h₁).mpr
      ((isPrecompositionEquivalence_iff_of_homotopy H₀ h₀).mp
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_id A))

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
