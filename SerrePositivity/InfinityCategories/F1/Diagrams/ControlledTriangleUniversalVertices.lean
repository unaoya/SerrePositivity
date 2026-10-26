module

public import SerrePositivity.InfinityCategories.F1.Diagrams.ControlledTriangleUniversalLongHom

/-!
概要：普遍長 Hom の各 L 頂点への制限と、直接 path の評価を厳密に回収する。
方針：fiber 包含の curry と元の functorVertex の逆対応を照合する。
規約：各 L 頂点で K の全単体を保持する。
使われ方：正規化全対角の入力を、読み出した同じ長 Hom 全族へ同定する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 中間点を含まない、直接 path {0,2}。 -/
abbrev triangleDirectPath : TriangleNativePath.{u} :=
  trianglePathFromInterval (ULift.up (0 : Fin 2))

lemma uliftTriangleNativePathIntervalIso_inv_first :
    uliftTriangleNativePathIntervalIso.{u, v}.inv.app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
        ULift.up (ComposableArrows.mk₀ triangleDirectPath.{u}) := by
  change ULift.up (triangleNativePathIntervalIso.inv.app (Opposite.op ⦋0⦌)
    (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) = _
  congr 1

lemma controlledTriangleUniversalLongHom_at_vertex
    (X Z : KanObject.{u}) (K : SSet.{u + 1})
    (c : K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom X Z))
    (l : (controlledTriangleLongHomSpace X Z K c) _⦋0⦌) :
    lift (𝟙 K) (SSet.const l) ≫ controlledTriangleUniversalLongHom X Z K c =
      controlledTriangleLongHomValue l := by
  have h := curry_app_vertex (controlledTriangleUniversalLongHom X Z K c) l
  rw [controlledTriangleUniversalLongHom, curry_uncurry] at h
  apply functorVertex_injective
  rw [show functorVertex (controlledTriangleLongHomValue l) = l.val from
    (functorVertexEquiv _ _).apply_symm_apply l.val]
  exact h.symm

lemma controlledTriangleUniversalInterval_at_vertex
    (X Z : KanObject.{u}) (K : SSet.{u + 1})
    (c : K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom X Z))
    (l : (controlledTriangleLongHomSpace X Z K c) _⦋0⦌) :
    lift (𝟙 K) (SSet.const l) ≫ controlledTriangleUniversalInterval X Z K c =
      controlledTriangleLongHomValue l ≫
        (pre (uliftTriangleNativePathIntervalIso.{u, u + 1}).inv).app _ := by
  rw [controlledTriangleUniversalInterval, ← Category.assoc,
    controlledTriangleUniversalLongHom_at_vertex]

/-- 同じ l の普遍区間の零端は、元の長 Hom 全族の直接 path 評価そのもの。 -/
lemma controlledTriangleUniversalInterval_direct_at_vertex
    (X Z : KanObject.{u}) (K : SSet.{u + 1})
    (c : K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom X Z))
    (l : (controlledTriangleLongHomSpace X Z K c) _⦋0⦌) :
    lift (𝟙 K) (SSet.const l) ≫
        (prismEndpoint 0 (K ⊗ controlledTriangleLongHomSpace X Z K c) ≫
          uncurry (controlledTriangleUniversalInterval X Z K c)) =
      controlledTriangleLongHomValue l ≫ evaluateFunctorAt
        (Y := (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom X Z))
        (ULift.up (ComposableArrows.mk₀ triangleDirectPath.{u})) := by
  have h := curry_evaluateFunctorAt_interval
    (uncurry (controlledTriangleUniversalInterval X Z K c)) (0 : Fin 2)
  rw [curry_uncurry] at h
  rw [← h, ← Category.assoc, controlledTriangleUniversalInterval_at_vertex,
    Category.assoc, evaluateFunctorAt_pre, uliftTriangleNativePathIntervalIso_inv_first]

end SerrePositivity.InfinityCategories
