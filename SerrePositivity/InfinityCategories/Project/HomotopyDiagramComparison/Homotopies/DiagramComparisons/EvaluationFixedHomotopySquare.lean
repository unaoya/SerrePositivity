module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.EvaluationFixedHomotopyTriangle

/-!
概要：同じ評価を全時刻固定する四つの実際の円柱の二経路は、同じ合成の類を持つ。
方針：評価への後合成の忠実性により、両方が恒等像を持つ二因子の合成を照合する。
規約：四円柱の代表を保持。使われ方：普遍前置・枝比較・元の根辺初期族の整合性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 評価固定の実際の四円柱の二経路は、同じ合成の射の類を持つ。 -/
lemma evaluationFixedHomotopySquare_homMk_comp {T E B : SSet.{u}}
    [KanComplex E] [Quasicategory B] (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p]
    {s a b c : T ⟶ E} (H₀ : SSet.Homotopy s a) (H₁ : SSet.Homotopy a b)
    (H₂ : SSet.Homotopy s c) (H₃ : SSet.Homotopy c b) (z : T ⟶ B)
    (h₀ : H₀.h ≫ p = fst T Δ[1] ≫ z) (h₁ : H₁.h ≫ p = fst T Δ[1] ≫ z)
    (h₂ : H₂.h ≫ p = fst T Δ[1] ≫ z) (h₃ : H₃.h ≫ p = fst T Δ[1] ≫ z) :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H₀) ≫
        SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H₁) =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H₂) ≫
        SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H₃) := by
  let I := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy H₀
  let J := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy H₁
  let K := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy H₂
  let L := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy H₃
  let F := (hoFunctor.map ((ihom T).map p)).toFunctor
  have hi := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyIso_postcomp_constant_arrow H₀ p z h₀
  have hj := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyIso_postcomp_constant_arrow H₁ p z h₁
  have hk := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyIso_postcomp_constant_arrow H₂ p z h₂
  have hl := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyIso_postcomp_constant_arrow H₃ p z h₃
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.functorIso_postcomp_hom] at hi hj hk hl
  have hij : Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (I ≪≫ J) p).hom =
      Arrow.mk (𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex z))) := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.functorIso_postcomp_hom]
    exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.functor_twoFactors_identity_arrow F I J _ hi hj
  have hkl : Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (K ≪≫ L) p).hom =
      Arrow.mk (𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex z))) := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.functorIso_postcomp_hom]
    exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.functor_twoFactors_identity_arrow F K L _ hk hl
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.trivialKanFibration_postcomp_iso_hom_injective p (I ≪≫ J) (K ≪≫ L) (hij.trans hkl.symm)

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
