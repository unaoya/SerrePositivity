module

public import SerrePositivity.InfinityCategories.HomotopyLimits.TrivialFibrationIsoFaithful
public import SerrePositivity.InfinityCategories.HomotopyLimits.ArrowIdentityComposition

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
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 同じ自明 Kan 評価上で定値な三円柱は、元の辺の類の三角形の合成則を満たす。 -/
lemma evaluationFixedHomotopyTriangle_homMk_comp {T E B : SSet.{u}}
    [KanComplex E] [Quasicategory B] (p : E ⟶ B) [TrivialKanFibration p]
    {s a b : T ⟶ E} (H₀ : SSet.Homotopy s a) (H₁ : SSet.Homotopy a b)
    (H₂ : SSet.Homotopy s b) (z : T ⟶ B)
    (h₀ : H₀.h ≫ p = fst T Δ[1] ≫ z) (h₁ : H₁.h ≫ p = fst T Δ[1] ≫ z)
    (h₂ : H₂.h ≫ p = fst T Δ[1] ≫ z) :
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H₀) ≫
        SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H₁) =
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H₂) := by
  let I := functorIsoOfSimplicialHomotopy H₀
  let J := functorIsoOfSimplicialHomotopy H₁
  let K := functorIsoOfSimplicialHomotopy H₂
  let F := (hoFunctor.map ((ihom T).map p)).toFunctor
  have hi : Arrow.mk (F.map I.hom) = Arrow.mk (𝟙 (HomotopyCategory.mk (functorVertex z))) :=
    homotopyIso_postcomp_constant_arrow H₀ p z h₀
  have hj : Arrow.mk (F.map J.hom) = Arrow.mk (𝟙 (HomotopyCategory.mk (functorVertex z))) :=
    homotopyIso_postcomp_constant_arrow H₁ p z h₁
  have hk := homotopyIso_postcomp_constant_arrow H₂ p z h₂
  have hij : Arrow.mk (FunctorIso.postcomp (I ≪≫ J) p).hom =
      Arrow.mk (𝟙 (HomotopyCategory.mk (functorVertex z))) := by
    rw [functorIso_postcomp_hom]
    exact functor_twoFactors_identity_arrow F I J _ hi hj
  exact trivialKanFibration_postcomp_iso_hom_injective p (I ≪≫ J) K (hij.trans hk.symm)

end SerrePositivity.InfinityCategories.HomotopyLimits
