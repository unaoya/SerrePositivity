module

public import SerrePositivity.KST.Spectra.FreePointedFunctionIso
public import SerrePositivity.KST.Spectra.GroupFunctionCochains
public import SerrePositivity.KST.Spectra.PointedWeightedEndUnderlyingWeight

/-!
概要：自由作用の点つき end の関数表示の重みの前合成への自然性。
方針：忘却後に end の比較と自由軌道の関数の座標式の可換性を合成する。
規約：点つき射の厳密な等式を示す。
使われ方：Goerss–Jardine VIII §2、HA §1.4.2。非斉次 cochain の点つき顔・退化の整合性。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory SSet

namespace SerrePositivity.KST.Spectra.FreeActionFamily

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {G : Type u} [Group G]

lemma pointedFunctionPre_id (S : Type u) (B : Action PointedSimplicialSet.{u} G) :
    pointedFunctionPre (𝟙 (Action.leftRegular G ⊗ Action.trivial G S)) B =
      𝟙 (SimplicialFunctionComplex.pointedObj S B.V) := by
  apply Under.UnderMorphism.ext
  exact functionPre_id S ((PointedSimplicialSet.forget.mapAction G).obj B)

lemma pointedFunctionPre_comp {S T U : Type u}
    (θ : (Action.leftRegular G ⊗ Action.trivial G T) ⟶
      (Action.leftRegular G ⊗ Action.trivial G S))
    (η : (Action.leftRegular G ⊗ Action.trivial G U) ⟶
      (Action.leftRegular G ⊗ Action.trivial G T)) (B : Action PointedSimplicialSet.{u} G) :
    pointedFunctionPre (η ≫ θ) B = pointedFunctionPre θ B ≫ pointedFunctionPre η B := by
  apply Under.UnderMorphism.ext
  exact functionPre_comp θ η ((PointedSimplicialSet.forget.mapAction G).obj B)

/-- 概要：自由軌道の点つき end の関数表示は軌道の射の前合成と可換。
方針：点つき end の忘却比較の自然性と関数表示の座標式の自然性を合成する。
規約：係数の Kan 性を要求しない。
使われ方：Goerss–Jardine VIII §2。点つき cochain の関数表示の余単体自然性。 -/
lemma pointedFunctionIso_pre {S T : Type u}
    (θ : (Action.leftRegular G ⊗ Action.trivial G T) ⟶
      (Action.leftRegular G ⊗ Action.trivial G S)) (B : Action PointedSimplicialSet.{u} G) :
    PointedWeightedEnd.preMap ((GroupActionCochains.actionWeightFunctor G).map θ)
        (pointedCoefficients B) ≫ (pointedFunctionIso T B).hom =
      (pointedFunctionIso S B).hom ≫ pointedFunctionPre θ B := by
  apply Under.UnderMorphism.ext
  let C := (PointedSimplicialSet.forget.mapAction G).obj B
  let D := pointedCoefficients B
  let j := (GroupActionCochains.actionWeightFunctor G).map θ
  change (PointedWeightedEnd.preMap j D).right ≫
      ((PointedWeightedEnd.underlyingIso (weight T) D).hom ≫ (functionIso T C).hom) =
    ((PointedWeightedEnd.underlyingIso (weight S) D).hom ≫ (functionIso S C).hom) ≫ functionPre θ C
  rw [← Category.assoc, PointedWeightedEnd.underlyingIso_preMap]
  change ((PointedWeightedEnd.underlyingIso (weight S) D).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre j (coefficients C)) ≫
        (functionIso T C).hom = _
  rw [Category.assoc, functionIso_pre, ← Category.assoc]

end

end SerrePositivity.KST.Spectra.FreeActionFamily
