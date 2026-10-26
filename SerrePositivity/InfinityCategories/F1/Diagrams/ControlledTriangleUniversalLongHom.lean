module

public import SerrePositivity.InfinityCategories.F1.Diagrams.ControlledTriangleEncoderMap
public import SerrePositivity.InfinityCategories.F1.Diagrams.TriangleDiagonalKanExtension
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FunctorFiber

/-!
概要：要求正本の長 Hom 空間 L の、同じ K 上の普遍長 Hom 全族とその区間表示。
方針：実際の fiber 包含を uncurry し、指定 full path を標準区間の終点へ移す。
規約：合成端を全 K・L で厳密に保持する。
使われ方：全族の再構成写像へ入力する普遍長 Hom。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 指定された実 L の普遍長 Hom 全族。 -/
def controlledTriangleUniversalLongHom (X Z : KanObject.{u}) (K : SSet.{u + 1})
    (c : K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom X Z)) :
    K ⊗ controlledTriangleLongHomSpace X Z K c ⟶
      (ihom ((SSet.uliftFunctor.{u + 1, u}).obj (nerve TriangleNativePath.{u}))).obj
        ((SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom X Z)) :=
  uncurry (vertexFiberι _ (functorVertex c))

lemma controlledTriangleUniversalLongHom_comp (X Z : KanObject.{u}) (K : SSet.{u + 1})
    (c : K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom X Z)) :
    controlledTriangleUniversalLongHom X Z K c ≫ evaluateFunctorAt
      (Y := (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom X Z))
      (ULift.up (ComposableArrows.mk₀ triangleFullPath.{u})) =
        fst K (controlledTriangleLongHomSpace X Z K c) ≫ c := by
  rw [controlledTriangleUniversalLongHom, ← uncurry_natural_right, vertexFiberι_comp,
    uncurry_const_functorVertex]

/-- 同じ普遍長 Hom を、同じ合成端を終点とする標準区間として表示する。 -/
def controlledTriangleUniversalInterval (X Z : KanObject.{u}) (K : SSet.{u + 1})
    (c : K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom X Z)) :
    K ⊗ controlledTriangleLongHomSpace X Z K c ⟶
      (ihom (Δ[1] : SSet.{u + 1})).obj
        ((SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom X Z)) :=
  controlledTriangleUniversalLongHom X Z K c ≫
    (pre (uliftTriangleNativePathIntervalIso.{u, u + 1}).inv).app _

lemma controlledTriangleUniversalInterval_comp (X Z : KanObject.{u}) (K : SSet.{u + 1})
    (c : K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom X Z)) :
    controlledTriangleUniversalInterval X Z K c ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
        fst K (controlledTriangleLongHomSpace X Z K c) ≫ c := by
  rw [controlledTriangleUniversalInterval, Category.assoc, evaluateFunctorAt_pre,
    uliftTriangleNativePathIntervalIso_inv_last, controlledTriangleUniversalLongHom_comp]

/-- 元の二短辺の合成を合成端とする普遍区間の、対角を保つ分離座標への延長。 -/
lemma controlledTriangleUniversalSeparatedExtension_exists
    (X Y Z : KanObject.{u}) (K : SSet.{u + 1})
    (f : K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom X Y))
    (g : K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom Y Z)) :
    let c := controlledTriangleCompositeFamily X Y Z K f g
    let L := controlledTriangleLongHomSpace X Z K c
    ∃ M : (Δ[1] : SSet.{u + 1}) ⊗ ((K ⊗ K) ⊗ L) ⟶
        (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom X Z),
      (Δ[1] ◁ triangleParameterDiagonal K L) ≫ M =
        uncurry (controlledTriangleUniversalInterval X Z K c) ∧
      prismEndpoint 1 ((K ⊗ K) ⊗ L) ≫ M =
        lift (fst (K ⊗ K) L ≫ fst K K ≫ f) (fst (K ⊗ K) L ≫ snd K K ≫ g) ≫
        (HomotopyLimits.uliftTensorIso.{u, u + 1}
          (SimplicialCategory.sHom X Y) (SimplicialCategory.sHom Y Z)).inv ≫
          (SSet.uliftFunctor.{u + 1, u}).map (eComp SSet X Y Z) := by
  dsimp only
  obtain ⟨M, hdiag, hend⟩ := triangleDiagonalKanExtension_uncurry_exists K
    (controlledTriangleLongHomSpace X Z K (controlledTriangleCompositeFamily X Y Z K f g))
    _ _ _ f g
    ((HomotopyLimits.uliftTensorIso.{u, u + 1}
      (SimplicialCategory.sHom X Y) (SimplicialCategory.sHom Y Z)).inv ≫
      (SSet.uliftFunctor.{u + 1, u}).map (eComp SSet X Y Z))
    (controlledTriangleUniversalInterval X Z K _) (controlledTriangleUniversalInterval_comp X Z K _)
  rw [curry_evaluateFunctorAt_interval] at hend
  exact ⟨M, hdiag, hend⟩

end SerrePositivity.InfinityCategories
