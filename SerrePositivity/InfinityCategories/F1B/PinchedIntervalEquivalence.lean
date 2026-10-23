module

public import SerrePositivity.InfinityCategories.F1B.PinchedIntervalNaturality
public import SerrePositivity.InfinityCategories.F1B.PinchedIntervalSection
public import SerrePositivity.InfinityCategories.F1.Joins.JoinDiagramRelativeExtension
public import SerrePositivity.InfinityCategories.F1.Equivalences.EquivalenceRetraction

/-!
概要：右 pinched 模型と区間模型の同値。
方針：F1 の右模型の計算を狭い依存上で用い、相対 join 延長に接続する。
規約：左模型・straightening のモジュールを import しない。
使われ方：Kerodon §4.6.5–4.6.6、Prop 6.2.1.17 の pinched 模型への移行。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.PinchedInterval


/-- 概要：右 pinched 模型から区間模型への比較射には厳密な左逆がある。
方針：区間模型全体の fat join 図式を、pinched 模型の部分族と両端を保って回収する。
規約：左逆との合成はホモトピーでなく射の等式。
使われ方：Kerodon §4.6.6、写像空間比較の同値の単位。 -/
lemma comparison_exists_retraction {X : SSet.{u}}
    [Quasicategory X] (x y : X _⦋0⦌) :
    ∃ r : intervalMappingSpace x y ⟶ pinchedHom x y,
      comparison x y ≫ r = 𝟙 _ := by
  let c := comparison x y
  let F := rightIntervalFatDiagram (𝟙 (intervalMappingSpace x y))
  let G := pinchedHomUncurry (𝟙 (pinchedHom x y))
  have hFG : fatJoinMap c (𝟙 (Δ[0] : SSet.{u})) ≫ F =
      fatJoinComparison (pinchedHom x y) Δ[0] ≫ G := by
    dsimp [F, G, c]
    rw [rightIntervalFatDiagram_precomp, Category.comp_id]
    simpa only [Category.id_comp] using rightIntervalFatDiagram_comparison (𝟙 (pinchedHom x y))
  obtain ⟨H, hH, hx, hy⟩ := exists_joinDiagram_relative_extension c F G hFG
  have hx' : joinInl (intervalMappingSpace x y) Δ[0] ≫ H = SSet.const x := by
    rw [hx]
    exact rightIntervalFatDiagram_inl _
  have hy' : joinInr (intervalMappingSpace x y) Δ[0] ≫ H = SSet.yonedaEquiv.symm y := by
    rw [hy]
    exact rightIntervalFatDiagram_inr _
  refine ⟨pinchedHomCurry H hx' hy', ?_⟩
  apply pinchedHomUncurry_injective
  rw [pinchedHomUncurry_precomp, pinchedHomUncurry_curry]
  exact hH

/-- 概要：右 pinched 模型の区間比較は quasicategory の同値。
方針：厳密な左逆と既存のホモトピー右逆を可逆二胞体で比較する。
規約：X は quasicategory、両写像空間は Kan 複体。
使われ方：Kerodon §4.6.6、coherent nerve の左右の写像空間の比較。 -/
lemma comparison_isQCatEquivalence {X : SSet.{u}}
    [Quasicategory X] (x y : X _⦋0⦌) :
    IsQCatEquivalence (comparison x y) := by
  obtain ⟨r, hr⟩ := comparison_exists_retraction x y
  obtain ⟨b, ⟨hb⟩⟩ := comparison_postcomp_essentiallySurjective
    (𝟙 (intervalMappingSpace x y))
  exact isQCatEquivalence_of_retraction_of_rightInverseIso _ r b hr hb


end SerrePositivity.InfinityCategories.PinchedInterval
