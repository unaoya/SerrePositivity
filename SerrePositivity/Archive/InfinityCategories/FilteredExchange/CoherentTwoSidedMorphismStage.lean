module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentTwoSidedConstantStage
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.EdgewiseRefinementConstantVertex
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.TwoSidedHomIntervals
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity

/-!
概要：固定 Kan 射の定値共通係数では、同じ全二側区間族は補間段階に依存しない。
方針：元の退化係数を定値射へ戻し、全次数で二側単体の段階独立性を使う。
規約：区間全体と実係数を保持。使われ方：固定射での二側比較の実辺の計算。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {K L : KanObject.{u}} (f : K ⟶ L)
local notation "H" => SimplicialCategory.sHom K L
local notation "z" => ULift.up (edgewiseRefinementVertex
  (SimplicialObject.σ H 0 (functorVertex f)))

/-- 元の固定射の同じ全二側区間族を、補間段階零の定値族へ厳密に戻す。 -/
lemma coherentTwoSidedHomIntervalFamily_morphism_stage :
    lift (𝟙 (Δ[1] : SSet.{u + 1})) (SSet.const z) ≫
      coherentTwoSidedHomIntervalFamily K L =
    lift (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) (SSet.const z) ≫
      coherentTwoSidedHomIntervalFamily K L := by
  apply intervalMappingUncurry_injective
  rw [intervalMappingUncurry_precomp, intervalMappingUncurry_precomp,
    coherentTwoSidedHomIntervalFamily_uncurry]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨t, s⟩
  change coherentTwoSidedHomSimplex
      (PinchedHom.constant (edgewiseRefinementVertex ((H).σ 0 (functorVertex f))) n)
      (stdSimplex.objEquiv t).toOrderHom (stdSimplex.objEquiv s).toOrderHom =
    coherentTwoSidedHomSimplex
      (PinchedHom.constant (edgewiseRefinementVertex ((H).σ 0 (functorVertex f))) n)
      (stdSimplex.objEquiv t).toOrderHom (OrderHom.const _ 0)
  rw [edgewiseRefinementVertex_degenerate_constant]
  exact coherentTwoSidedHomSimplex_constant_stage _ _ _ _

/-- 同じ固定射の全補間区間は、その同じ零成分に定値な実射である。 -/
lemma coherentTwoSidedHomIntervalFamily_morphism_constant :
    lift (𝟙 (Δ[1] : SSet.{u + 1})) (SSet.const z) ≫
      coherentTwoSidedHomIntervalFamily K L =
    SSet.const ((coherentTwoSidedHomIntervalFamily K L).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2), z)) := by
  rw [coherentTwoSidedHomIntervalFamily_morphism_stage]
  have hc : lift (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) :
      (Δ[1] : SSet.{u + 1}) ⟶ Δ[1])
      (SSet.const z : (Δ[1] : SSet.{u + 1}) ⟶
        (SSet.uliftFunctor.{u + 1, u}).obj (edgewiseSubdivision H)) =
      SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2), z) := by
    apply SSet.hom_ext
    intro n
    rfl
  rw [hc, SSet.const_comp]

end SerrePositivity.InfinityCategories.F2
