module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativeExtensionCurryRestriction
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativeCurryHomVertexEvaluation
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.TriangleTargetFiberCoordinates

/-!
概要：相対延長を辺の切断へ curry した後の終点評価を、同じ全延長の終点制限へ戻す。
方針：普遍相対 curry の点評価を展開し、底上の前合成の元の座標を照合する。
規約：全パラメータと指定点を保持。使われ方：全三角形の二面での指定像の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 相対延長の切断族を指定点で評価すると、同じ全延長の同じ点への制限になる。 -/
lemma relativeExtensionCurryRestriction_evaluate_ι {T I K A E B : SSet.{u}}
    (p : E ⟶ B) (d : T ⟶ B) (i : I ⟶ T) (v : I ⟶ E) (hv : v ≫ p = i ≫ d)
    (j : K ⊗ A ⟶ T) (e : K ⟶ B) (hj : j ≫ d = fst K A ≫ e) (k : K _⦋0⦌) :
    uncurry (relativeExtensionCurryRestriction p d i v hv j e hj) ≫
        relativeFunctorEvaluate p e k ≫ vertexFiberι p (e.app (Opposite.op ⦋0⦌) k) =
      ((lift (SSet.const k) (𝟙 A) ≫ j) ▷
        relativeFunctorExtensionSpace p d i v hv) ≫
          relativeFunctorUncurry (relativeFunctorExtensionSpaceι p d i v hv) := by
  unfold relativeExtensionCurryRestriction
  simp only [uncurry_natural_left, Category.assoc]
  rw [relativeFunctorCurryHom_evaluate_ι]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨x, h⟩
  rfl

/-- 元の小さい fiber への終点評価も、同じ全延長の終点の pointed 座標を保つ。 -/
lemma relativeExtensionCurryRestriction_target_pointed {B : SSet.{u}} {T I A : SSet.{u + 1}}
    (J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) (b : B _⦋0⦌)
    (d : T ⟶ SpaceInfinity.{u}) (i : I ⟶ T) (v : I ⟶ PointedSpaceInfinity.{u})
    (hv : v ≫ pointedSpaceProjection = i ≫ d)
    (j : (Δ[1] : SSet.{u + 1}) ⊗ A ⟶ T) (e : (Δ[1] : SSet.{u + 1}) ⟶ SpaceInfinity.{u})
    (hj : j ≫ d = fst Δ[1] A ≫ e)
    (he : e.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 1) = J.app _ (ULift.up b)) :
    uncurry (relativeExtensionCurryRestriction pointedSpaceProjection d i v hv j e hj ≫
      (ihom A).map (pointedSectionTargetFiber J b e he)) ≫
        coherentCospanFiberPointedSource J b =
      ((prismEndpoint 1 A ≫ j) ▷
        relativeFunctorExtensionSpace pointedSpaceProjection d i v hv) ≫
          relativeFunctorUncurry
            (relativeFunctorExtensionSpaceι pointedSpaceProjection d i v hv) := by
  have hc : pointedSectionTargetFiber J b e he ≫ coherentCospanFiberPointedSource J b =
      relativeFunctorEvaluate pointedSpaceProjection e (stdSimplex.obj₀Equiv.symm 1) ≫
        vertexFiberι pointedSpaceProjection (e.app _ (stdSimplex.obj₀Equiv.symm 1)) := by
    rw [← coherentFiberPointedSourceIso_hom_ι J b]
    exact pointedSectionTargetFiber_pointed J b e he
  rw [uncurry_natural_right, Category.assoc, hc]
  exact relativeExtensionCurryRestriction_evaluate_ι _ _ _ _ _ _ _ _ _

end SerrePositivity.InfinityCategories.F2
