module

public import SerrePositivity.InfinityCategories.F1.Coherent.ConstantSourceComparison
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorExponentialEvaluation
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorSquarePost
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorPostUncurry
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativeConstFiberEvaluation

/-!
概要：定値始域の相対比較を、元の底を保つ全評価と厳密に結ぶ。
方針：指数則・切断表示・底上の前合成の三段階の評価式を使う。
規約：底・fiber・全追加パラメータを保持する。
使われ方：全 Hom の相対合成を全切断への後合成に移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 定値始域比較を全切断として評価すると、元の定値全空間の相対評価を回収する。 -/
lemma constantUnstraighteningSourceRelativeIso_evaluation {B T : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) (z : SpaceInfinity.{u} _⦋0⦌)
    (k : T ⟶ relativeFunctorSpace (leftUnstraighteningProjection F)
      (leftUnstraighteningProjection (SSet.const z))) :
    (B ◁ uncurry (k ≫ (constantUnstraighteningSourceRelativeIso F z).hom)) ≫
        HomotopyLimits.simplicialSectionsEvaluation (leftUnstraighteningProjection F) =
      (α_ B (vertexFiber pointedSpaceProjection z) T).inv ≫
        ((constantUnstraighteningSourceOverIso B z).inv.left ▷ T) ≫ relativeFunctorUncurry k := by
  let s := (k ≫ (relativeFunctorOverIso (constantUnstraighteningSourceOverIso B z)
      (Iso.refl (Over.mk (leftUnstraighteningProjection F)))).hom) ≫
    (eqToIso (congrArg (relativeFunctorSpace (leftUnstraighteningProjection F))
      (Category.comp_id (fst B (vertexFiber pointedSpaceProjection z))).symm)).hom
  change (B ◁ uncurry ((s ≫ (relativeFunctorExponentialIso
      (leftUnstraighteningProjection F) (𝟙 B) (vertexFiber pointedSpaceProjection z)).hom) ≫
        (ihom (vertexFiber pointedSpaceProjection z)).map
          (HomotopyLimits.simplicialSectionsRelativeIso (leftUnstraighteningProjection F)).inv)) ≫
      _ = _
  rw [uncurry_natural_right,
    simplicialSectionsRelativeIso_inv_evaluation, relativeFunctorExponentialIso_evaluation]
  dsimp only [s]
  rw [F2.relativeFunctorUncurry_transport]
  rw [relativeFunctorOverIso_hom]
  simp only [Iso.refl_hom, Over.id_left, relativeFunctorPost_id, Category.comp_id]
  · exact congrArg (fun q ↦ (α_ B (vertexFiber pointedSpaceProjection z) T).inv ≫ q)
      (relativeFunctorOverPre_uncurry (leftUnstraighteningProjection F)
        (constantUnstraighteningSourceOverIso B z).inv k)
  · simp only [Category.comp_id]
    rfl

end SerrePositivity.InfinityCategories
