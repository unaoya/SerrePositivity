module

public import SerrePositivity.InfinityCategories.F1.LeftUnstraighteningCompositionLift

/-!
概要：coherent な三角形に沿う unstraightening の変換の合成則。
方針：二辺の射の合成を終点とする長辺の持ち上げを、選択した長辺の射と比較する。
規約：同型は底を固定した相対写像空間内で取る。
使われ方：Kerodon Corollary 5.6.0.6、unstraightening の変換への作用の合成との整合性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：選択した unstraightening の変換の射は、任意の具体的な持ち上げの終点と底上で同型。
方針：具体的な持ち上げを選択空間の頂点にし、終点の同型を通常の射の相対頂点へ移す。
規約：底上の可換性と prism の両端の条件を厳密に固定する。
使われ方：Kerodon Corollary 5.6.0.6、恒等・合成の具体的な証人との比較。 -/
noncomputable def leftUnstraighteningTransformationMap_witnessIso
    {B : SSet.{u + 1}} (F G : B ⟶ SpaceInfinity.{u})
    (H : (Δ[1] : SSet.{u + 1}) ⊗ B ⟶ SpaceInfinity.{u})
    (h₀ : prismEndpoint 0 B ≫ H = F) (h₁ : prismEndpoint 1 B ≫ H = G)
    (W : (Δ[1] : SSet.{u + 1}) ⊗ leftUnstraightening F ⟶ PointedSpaceInfinity.{u})
    (hW₀ : prismEndpoint 0 _ ≫ W = pullback.fst pointedSpaceProjection F)
    (hWp : W ≫ pointedSpaceProjection = (Δ[1] ◁ leftUnstraighteningProjection F) ≫ H)
    (g : leftUnstraightening F ⟶ leftUnstraightening G)
    (hg : g ≫ leftUnstraighteningProjection G = leftUnstraighteningProjection F)
    (hW₁ : prismEndpoint 1 _ ≫ W = g ≫ pullback.fst pointedSpaceProjection G) :
    VertexIso (relativeFunctorVertex (leftUnstraighteningProjection G)
      (leftUnstraighteningProjection F) (leftUnstraighteningTransformationMap F G H h₀ h₁).val
        (leftUnstraighteningTransformationMap F G H h₀ h₁).property)
      (relativeFunctorVertex (leftUnstraighteningProjection G) (leftUnstraighteningProjection F)
        g hg) :=
  leftUnstraighteningTransformationMapChoiceIso F G H h₀ h₁
    (leftUnstraighteningTransformationWitness F H h₀ W hW₀ hWp) ≪≫
      eqToIso (congrArg SSet.HomotopyCategory.mk
        (leftUnstraighteningTransformationWitness_endpoint F G H h₀ h₁ W hW₀ hWp g hg hW₁))

/-- 概要：coherent な三角形の長辺の unstraightening の射は二辺の射の合成と底上で同型。
方針：内ホーンの積を充填して得た長辺の持ち上げを、可縮な選択空間で比較する。
規約：底 B は任意。単なる全空間の同型に弱めない。
使われ方：Kerodon Corollary 5.6.0.6、変換の合成との整合性。 -/
noncomputable def leftUnstraighteningTransformationMap_compositionIso
    {B : SSet.{u + 1}} (F G J : B ⟶ SpaceInfinity.{u})
    (α β γ : (Δ[1] : SSet.{u + 1}) ⊗ B ⟶ SpaceInfinity.{u})
    (hα₀ : prismEndpoint 0 B ≫ α = F) (hα₁ : prismEndpoint 1 B ≫ α = G)
    (hβ₀ : prismEndpoint 0 B ≫ β = G) (hβ₁ : prismEndpoint 1 B ≫ β = J)
    (hγ₀ : prismEndpoint 0 B ≫ γ = F) (hγ₁ : prismEndpoint 1 B ≫ γ = J)
    (T : (Δ[2] : SSet.{u + 1}) ⊗ B ⟶ SpaceInfinity.{u})
    (hTα : (stdSimplex.δ (2 : Fin 3) ▷ B) ≫ T = α)
    (hTβ : (stdSimplex.δ (0 : Fin 3) ▷ B) ≫ T = β)
    (hTγ : (stdSimplex.δ (1 : Fin 3) ▷ B) ≫ T = γ) :
    VertexIso (relativeFunctorVertex (leftUnstraighteningProjection J)
      (leftUnstraighteningProjection F) (leftUnstraighteningTransformationMap F J γ hγ₀ hγ₁).val
        (leftUnstraighteningTransformationMap F J γ hγ₀ hγ₁).property)
      (relativeFunctorVertex (leftUnstraighteningProjection J) (leftUnstraighteningProjection F)
        ((leftUnstraighteningTransformationMap F G α hα₀ hα₁).val ≫
          (leftUnstraighteningTransformationMap G J β hβ₀ hβ₁).val) (by
            rw [Category.assoc, (leftUnstraighteningTransformationMap G J β hβ₀ hβ₁).property,
              (leftUnstraighteningTransformationMap F G α hα₀ hα₁).property])) := by
  let h := exists_leftUnstraighteningTransformationComposite_lift
    F G J α β γ hα₀ hα₁ hβ₀ hβ₁ T hTα hTβ hTγ
  exact leftUnstraighteningTransformationMap_witnessIso F J γ hγ₀ hγ₁ h.choose
    h.choose_spec.1 h.choose_spec.2.2 _ _ h.choose_spec.2.1

end SerrePositivity.InfinityCategories
