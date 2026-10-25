module

public import SerrePositivity.InfinityCategories.F1.Diagrams.TriangleNativeCompositeValue
public import SerrePositivity.InfinityCategories.F1.Diagrams.ControlledTriangleLongHomFamily

/-!
概要：固定した元の二短辺を持つ任意の二胞体族から、合成端固定の長 Hom 全族を読む。
方針：全入力の全 native Hom を読み、合成端評価の零骨格指定持ち上げを使う。
規約：同じ K 全体への射を構成する。各点での同値だけから全族を結論しない。
使われ方：Ind-S (9) の longHom の各頂点の指定値。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 元の二短辺の全族を持つ二胞体族から、全 native Hom を各入力で回収する長 Hom 全族。 -/
lemma controlledTriangleFamily_exists_native_readout
    (X Y Z : KanObject.{u}) (K : SSet.{u + 1})
    (f : K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom X Y))
    (g : K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom Y Z))
    (F : (Δ[2] : SSet.{u + 1}) ⊗ K ⟶ SpaceInfinity.{u})
    (hf : (stdSimplex.δ (2 : Fin 3) ▷ K) ≫ F =
      (Δ[1] ◁ f) ≫ intervalMappingUncurry (coherentHomIntervalComparison X Y))
    (hg : (stdSimplex.δ (0 : Fin 3) ▷ K) ≫ F =
      (Δ[1] ◁ g) ≫ intervalMappingUncurry (coherentHomIntervalComparison Y Z)) :
    ∃ q : K ⟶ (ihom ((SSet.uliftFunctor.{u + 1, u}).obj (nerve TriangleNativePath.{u}))).obj
      ((SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom X Z)),
      q ≫ evaluateFunctorAt
        (X := (SSet.uliftFunctor.{u + 1, u}).obj (nerve TriangleNativePath.{u}))
        (Y := (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom X Z))
        (ULift.up (ComposableArrows.mk₀ triangleFullPath)) =
          lift f g ≫ (HomotopyLimits.uliftTensorIso.{u, u + 1}
            (SimplicialCategory.sHom X Y) (SimplicialCategory.sHom Y Z)).inv ≫
            (SSet.uliftFunctor.{u + 1, u}).map (eComp SSet.{u} X Y Z) ∧
      ∀ k : K _⦋0⦌,
        HEq (q.app (Opposite.op ⦋0⦌) k)
          (functorVertex ((SSet.uliftFunctor.{u + 1, u}).map
            ((SSet.yonedaEquiv (familyAtVertex F k)).map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩))) := by
  let t (k : K _⦋0⦌) := SSet.yonedaEquiv (familyAtVertex F k)
  let ff (k : K _⦋0⦌) := (SimplicialCategory.homEquiv' X Y).symm
    (f.app (Opposite.op ⦋0⦌) k).down
  let gg (k : K _⦋0⦌) := (SimplicialCategory.homEquiv' Y Z).symm
    (g.app (Opposite.op ⦋0⦌) k).down
  have hv (k : K _⦋0⦌) := triangleNativeHom_exists_of_faces (t k) (ff k) (gg k) (by
      dsimp only [t]
      erw [← stdSimplex.yonedaEquiv_δ_comp, ← familyAtVertex_precomp, hf,
        coherentHomIntervalFamily_vertex, Equiv.apply_symm_apply]) (by
      dsimp only [t]
      erw [← stdSimplex.yonedaEquiv_δ_comp, ← familyAtVertex_precomp, hg,
        coherentHomIntervalFamily_vertex, Equiv.apply_symm_apply])
  choose m hnative hfull using fun k => (hv k).2.2
  let c := lift f g ≫ (HomotopyLimits.uliftTensorIso.{u, u + 1}
    (SimplicialCategory.sHom X Y) (SimplicialCategory.sHom Y Z)).inv ≫
      (SSet.uliftFunctor.{u + 1, u}).map (eComp SSet.{u} X Y Z)
  obtain ⟨q, hq, hvertices⟩ := triangleLongHomFamily_exists_with_vertices.{u, u + 1}
    ((SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom X Z)) K c
    (fun k => functorVertex ((SSet.uliftFunctor.{u + 1, u}).map (m k))) (by
      intro k
      rw [evaluateFunctorAt_functorVertex]
      change ULift.up ((m k).app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ triangleFullPath)) =
        ULift.up ((eComp SSet X Y Z).app (Opposite.op ⦋0⦌)
          ((f.app (Opposite.op ⦋0⦌) k).down, (g.app (Opposite.op ⦋0⦌) k).down))
      rw [hfull, simplicialHom_vertex_comp]
      dsimp only [ff, gg]
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply])
  refine ⟨q, hq, ?_⟩
  intro k
  rw [hvertices]
  exact (uliftHomFunctorVertex_heq.{u, u + 1}
    (congrArg₂ SimplicialCategory.sHom (hv k).1 (hv k).2.1) _ _ (hnative k)).symm

end SerrePositivity.InfinityCategories
