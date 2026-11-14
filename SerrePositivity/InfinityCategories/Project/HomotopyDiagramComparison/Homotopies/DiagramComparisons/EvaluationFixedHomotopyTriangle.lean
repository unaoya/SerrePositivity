module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.TrivialFibrationIsoFaithful
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.ArrowIdentityComposition

/-!
概要：同じ評価を全時刻固定する三つの実際の円柱の類は、同じ三角形の合成則を満たす。
方針：自明 Kan 評価の h Fun 上の忠実性で、恒等像を持つ二つの射を比較する。
規約：全時刻の評価固定を要求する。使われ方：元の左右の Hom 円柱の経路整合性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 同じ自明 Kan 評価上で定値な三円柱は、元の辺の類の三角形の合成則を満たす。 -/
lemma evaluationFixedHomotopyTriangle_homMk_comp {T E B : SSet.{u}}
    [KanComplex E] [Quasicategory B] (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p]
    {s a b : T ⟶ E} (H₀ : SSet.Homotopy s a) (H₁ : SSet.Homotopy a b)
    (H₂ : SSet.Homotopy s b) (z : T ⟶ B)
    (h₀ : H₀.h ≫ p = fst T Δ[1] ≫ z) (h₁ : H₁.h ≫ p = fst T Δ[1] ≫ z)
    (h₂ : H₂.h ≫ p = fst T Δ[1] ≫ z) :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H₀) ≫
        SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H₁) =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H₂) := by
  let I := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy H₀
  let J := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy H₁
  let K := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy H₂
  let F := (hoFunctor.map ((ihom T).map p)).toFunctor
  have hi : Arrow.mk (F.map I.hom) = Arrow.mk (𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex z))) :=
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyIso_postcomp_constant_arrow H₀ p z h₀
  have hj : Arrow.mk (F.map J.hom) = Arrow.mk (𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex z))) :=
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyIso_postcomp_constant_arrow H₁ p z h₁
  have hk := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyIso_postcomp_constant_arrow H₂ p z h₂
  have hij : Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (I ≪≫ J) p).hom =
      Arrow.mk (𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex z))) := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.functorIso_postcomp_hom]
    exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.functor_twoFactors_identity_arrow F I J _ hi hj
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.trivialKanFibration_postcomp_iso_hom_injective p (I ≪≫ J) K (hij.trans hk.symm)

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
