module

public import SerrePositivity.InfinityCategories.F2.CoherentTwoSidedMorphismStage
public import SerrePositivity.InfinityCategories.F2.CoherentKanTwoSidedIntervalHomotopy
public import SerrePositivity.InfinityCategories.F2.HomotopyConstantComponent

/-!
概要：固定した元の Kan 射で、元の二側比較の成分は恒等の類である。
方針：同じ全補間が実際に定値であることを、元の実成分辺へ適用する。
規約：区間の端点と指定円柱を保持。使われ方：固定射の値比較の因子の除去。
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

/-- 元の退化 Hom 係数での指定二側区間比較の成分は、実終点での恒等の値。 -/
lemma coherentKanTwoSidedIntervalIso_morphism_heq_refl :
    HEq ((coherentKanTwoSidedIntervalIso K L).app z)
      (Iso.refl (SSet.HomotopyCategory.mk
        (((SSet.uliftFunctor.{u + 1, u}).map (edgewiseRight H) ≫
          coherentKanRightHomInterval K L).app (Opposite.op ⦋0⦌) z))) := by
  let N := intervalMappingPostOfEq (𝟙 SpaceInfinity.{u})
    (coherentNerveVertex K) (coherentNerveVertex L)
    (spaceInfinityVertex_eq_coherent K).symm (spaceInfinityVertex_eq_coherent L).symm
  let T := coherentKanTwoSidedIntervalHomotopy K L
  let y := N.app (Opposite.op ⦋0⦌)
    ((coherentTwoSidedHomIntervalFamily K L).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2), z))
  have hc : lift (SSet.const z) (𝟙 (Δ[1] : SSet.{u + 1})) ≫ T.h = SSet.const y := by
    change (lift (SSet.const z) (𝟙 (Δ[1] : SSet.{u + 1})) ≫ (β_ _ _).hom ≫
      coherentTwoSidedHomIntervalFamily K L) ≫ N = _
    rw [lift_braiding_hom_assoc, coherentTwoSidedHomIntervalFamily_morphism_constant,
      SSet.const_comp]
  have hi := homotopyIso_app_heq_refl_of_degenerate T z y
    (homotopyEvaluatedEdge_degenerate_of_constant T z y hc)
  rw [coherentKanTwoSidedIntervalIso_eq_homotopy]
  exact hi

end SerrePositivity.InfinityCategories.F2
