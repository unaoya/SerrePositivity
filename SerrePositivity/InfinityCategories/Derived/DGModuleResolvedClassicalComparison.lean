module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedSourceHomotopy
public import SerrePositivity.InfinityCategories.Derived.DGSemifreeClassicalComparison
/-!
概要：実出力分解の通常の h 上の作用を、同じ H⁰ の出力分解へ自然同型で比較する。
方針：指定切断の比較と実半自由出力射影の自然性を合成する。
規約：元の出力の射影性は不要。使われ方：一般 kernel ∞ 関手の主導来作用への照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [DGCategory R C]
  (E : Type v) [DGCategory R E] [Small.{u} E]
/-- 元の実出力分解の通常の h 上の作用を、同じ主導来比較へ送る。 -/
def dgModuleResolvedInfinity_classicalIso
    (F : DGFunctor R C (RightModule R E)) :
    (hoFunctor.map (dgModuleResolvedInfinity R C E F)).toFunctor ⋙
      (dgStableHomotopyEquivalence R (SemifreeDGModules R E)).functor ⋙
        dgSemifreeModuleToDerived R E ≅
    (dgStableHomotopyEquivalence R C).functor ⋙
      dgModuleOutputResolutionClassical R C E F := by
  let S := dgNerve.map
      (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C) ≫
        (dgModuleFunctorResolutionSourceNerveEquivalence R C E F).inv
  let G := dgModuleFunctorResolutionReplacement R C E F
  have h : dgModuleResolvedInfinity R C E F = S ≫ dgNerve.map G := by
    simpa only [S, G, Category.assoc] using
      dgModuleResolvedInfinity_eq_section_replacement R C E F
  rw [h, hoFunctor.map_comp]
  change ((hoFunctor.map S).toFunctor ⋙ (hoFunctor.map (dgNerve.map G)).toFunctor) ⋙ _ ≅ _
  exact Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (hoFunctor.map S).toFunctor
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (dgStableHomotopyEquivalence_naturalityIso R _ _ G)
          (dgSemifreeModuleToDerived R E) ≪≫ Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (dgModuleResolvedSourceSection_homotopyIso R C E F)
      (G.onHomotopy ⋙ dgSemifreeModuleToDerived R E) ≪≫
    Functor.associator _ _ _
end SerrePositivity.InfinityCategories
