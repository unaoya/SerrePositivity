module

public import SerrePositivity.InfinityCategories.Sheaves.SheafFiniteLimits
public import SerrePositivity.InfinityCategories.Sheaves.SheafCoefficientEquivalence
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.FunctorLoopEquivalence
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopSourcePresentation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FullSubcomplexInternalHom

/-!
概要：層の全 loop 族の四つの角が、元の層の頂点条件を満たすことを確認する。
方針：終点は元の層、始点は係数の loop 同値、残る二角は周囲の零頂点を使う。
  文献対応：HA §1.1.3、Kerodon §7.1（Tag 02H1）の安定な層の部分圏。
規約：既存の関手圏の全 loop 族を使い、対象ごとの選択で全族を代用しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.HA.StableInfinityCategories
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E]
variable [HasFiniteLimits E]

/-- 元の層の包含を、既存の関手圏の全 loop 族に入れる。 -/
def sheafAmbientLoopFamily (J : GrothendieckTopology C) (s : E ⟶ loopDiagrams E) :
    SheafCat J E ⟶ loopDiagrams (PresheafCat C E) :=
  sheafInclusion J ≫ functorLoopSection (presheafShape C) s

/-- 四つの角の全評価は、元の係数での同じ角の全後合成。 -/
lemma sheafAmbientLoopFamily_evaluation (J : GrothendieckTopology C)
    (s : E ⟶ loopDiagrams E) (i j : Fin 2) :
    sheafAmbientLoopFamily J s ≫ loopDiagramEvaluation (PresheafCat C E) i j =
      sheafInclusion J ≫ (ihom (presheafShape C)).map (s ≫ loopDiagramEvaluation E i j) := by
  rw [sheafAmbientLoopFamily, Category.assoc, functorLoopSection_evaluation]

/-- 終点が恒等である同じ係数の loop 切断は、全層族でも終点を厳密に保つ。 -/
lemma sheafAmbientLoopFamily_target (J : GrothendieckTopology C)
    (s : E ⟶ loopDiagrams E) (hs : s ≫ loopDiagramEvaluation E 1 1 = 𝟙 E) :
    sheafAmbientLoopFamily J s ≫ loopDiagramEvaluation (PresheafCat C E) 1 1 =
      sheafInclusion J := by
  rw [sheafAmbientLoopFamily_evaluation, hs, CategoryTheory.Functor.map_id, Category.comp_id]

/-- 指定 loop 同値の全層族の四つの角はすべて層。 -/
lemma sheafAmbientLoopFamily_corner_isSheaf (J : GrothendieckTopology C)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    (s : E ⟶ loopDiagrams E) (hs : s ≫ loopDiagramEvaluation E 1 1 = 𝟙 E)
    (hΩ : IsQCatEquivalence (s ≫ loopDiagramEvaluation E 0 0))
    (x : (SheafCat J E) _⦋0⦌) (i j : Fin 2) :
    sheafProperty J ((loopDiagramEvaluation (PresheafCat C E) i j).app _
      ((sheafAmbientLoopFamily J s).app _ x)) := by
  fin_cases i <;> fin_cases j
  · have h := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) x)
      (sheafAmbientLoopFamily_evaluation J s 0 0)
    exact (congrArg (sheafProperty J) h).mpr
      ((sheafProperty_postcomp_equivalence_iff J hΩ.choose x.val).mpr
        (fullSubcomplexOnVertices_vertex x))
  · rw [loopDiagramVertex_evaluation]
    exact sheafProperty_of_isTerminalVertex J hE _
      (fullSubcomplexOnVertices_vertex ((sheafAmbientLoopFamily J s).app _ x)).1.2
  · rw [loopDiagramVertex_evaluation]
    exact sheafProperty_of_isTerminalVertex J hE _
      (fullSubcomplexOnVertices_vertex ((sheafAmbientLoopFamily J s).app _ x)).2.1.2
  · have h := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) x)
      (sheafAmbientLoopFamily_target J s hs)
    exact (congrArg (sheafProperty J) h).mpr (fullSubcomplexOnVertices_vertex x)

/-- 元の loop 四角形の全頂点が層であるという、内部 Hom の持ち上げに必要な条件。 -/
lemma sheafAmbientLoopFamily_vertices (J : GrothendieckTopology C)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    (s : E ⟶ loopDiagrams E) (hs : s ≫ loopDiagramEvaluation E 1 1 = 𝟙 E)
    (hΩ : IsQCatEquivalence (s ≫ loopDiagramEvaluation E 0 0))
    (x : (SheafCat J E) _⦋0⦌) :
    FunctorVertexSatisfies ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1]) (PresheafCat C E)
      (sheafProperty J) ((sheafAmbientLoopFamily J s).app _ x).val := by
  rintro ⟨i, j⟩
  obtain ⟨i, rfl⟩ := (stdSimplex.obj₀Equiv).symm.surjective i
  obtain ⟨j, rfl⟩ := (stdSimplex.obj₀Equiv).symm.surjective j
  exact sheafAmbientLoopFamily_corner_isSheaf J hE s hs hΩ x i j

end SerrePositivity.InfinityCategories.Sheaves
