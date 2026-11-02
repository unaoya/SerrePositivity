module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitApexCoefficientMap
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceSimplexPointedFamilyRestriction
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitRawUniversalTrianglePrism

/-!
概要：元の raw 普遍三角形を、同じ全係数の明示的な pointed 族と比較する。
方針：同じ全三角形と初点を厳密に回収し、同じ可縮な相対延長空間へ入れる。
規約：元の指定普遍三角形を置き換えない。使われ方：四因子境界の元の比較への反映。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b d)
local notation "s" => coherentColimitApexTriangle B T
local notation "q" => coherentColimitApexCoefficientMap B T
local notation "A" => spaceSimplexPointedCoefficients s

/-- 元の普遍三角形の全係数制限も、同じ元の余極限全三角形を厳密に被覆する。 -/
lemma coherentColimitApexPointedFamily_projection :
    coherentColimitRawUniversalTrianglePrism B T q ≫ pointedSpaceProjection =
      fst Δ[2] A ≫ SSet.yonedaEquiv.symm s := by
  rw [coherentColimitRawUniversalTrianglePrism_projection, coherentColimitApexTriangle,
    Equiv.symm_apply_apply]

/-- 元の普遍三角形の初点は、同じ全 Hom 係数の元の標準 fiber 比較。 -/
lemma coherentColimitApexPointedFamily_initial :
    (scaffoldFirstVertex 2 ▷ A) ≫ coherentColimitRawUniversalTrianglePrism B T q =
      snd Δ[0] A ≫ pointedCoherentFiberComparison
        (EnrichedFunctor.obj s ⟨ULift.up 0⟩) ≫ vertexFiberι pointedSpaceProjection
          (coherentNerveVertex (EnrichedFunctor.obj s ⟨ULift.up 0⟩)) := by
  have hi : prismEndpoint 0 A ≫ (stdSimplex.δ (1 : Fin 3) ▷ A) =
      lift (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 3))) (𝟙 A) := by
    rw [prismEndpoint, lift_whiskerRight, SSet.const_comp]
    rfl
  rw [scaffoldFirstVertex_tensor_lift, ← hi]
  have he := congrArg (fun m => snd Δ[0] A ≫ m)
    (coherentColimitRawUniversalTrianglePrism_long_start B T q)
  have hq := congrArg (fun m => snd Δ[0] A ≫ m)
    (coherentColimitApexCoefficientMap_ι B T)
  simpa only [Category.assoc] using he.trans hq

/-- 元の指定普遍三角形と明示した全 pointed 族の、同じ相対延長空間内の比較。 -/
def coherentColimitApexPointedFamilyComparisonIso :=
  spaceSimplexPointedFamilyComparisonIso s (coherentColimitRawUniversalTrianglePrism B T q)
    (coherentColimitApexPointedFamily_projection B T)
    (coherentColimitApexPointedFamily_initial B T)

/-- 元の同じ普遍三角形との全比較を、任意の部分図式へ底を保って写す。 -/
def coherentColimitApexPointedFamilyRestrictionIso {C : SSet.{u + 1}}
    (r : C ⟶ (Δ[2] : SSet.{u + 1}) ⊗ A) :=
  spaceSimplexPointedFamilyRestrictionIso s (coherentColimitRawUniversalTrianglePrism B T q)
    (coherentColimitApexPointedFamily_projection B T)
    (coherentColimitApexPointedFamily_initial B T) r

end SerrePositivity.InfinityCategories.F2
