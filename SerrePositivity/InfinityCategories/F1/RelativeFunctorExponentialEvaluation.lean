module

public import SerrePositivity.InfinityCategories.F1.RelativeFunctorExponential
public import SerrePositivity.InfinityCategories.F1.RelativeFunctorBaseChange
public import SerrePositivity.InfinityCategories.HomotopyLimits.SectionsKan

/-!
概要：相対関手の指数則と全切断表示を、元の全評価で計算する。
方針：二段の curry の往復と相対評価の自然性を使う。
規約：任意の底・射影・追加パラメータを保持する。
使われ方：定値始域比較の合成に関する厳密な照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories

/-- 相対指数則の二重評価は、同じ元の評価の結合子による並べ替え。 -/
lemma relativeFunctorExponentialIso_evaluation {A E B L T : SSet.{u}}
    (p : E ⟶ B) (a : A ⟶ B)
    (k : T ⟶ relativeFunctorSpace p (fst A L ≫ a)) :
    relativeFunctorUncurry (uncurry (k ≫ (relativeFunctorExponentialIso p a L).hom)) =
      (α_ A L T).inv ≫ relativeFunctorUncurry k := by
  change relativeFunctorUncurry (uncurry (k ≫ relativeFunctorCurryHom p a L)) = _
  rw [uncurry_natural_left, relativeFunctorCurryHom, uncurry_curry,
    relativeFunctorUncurry_naturality, relativeFunctorUncurry_curry,
    ← Category.assoc, associator_inv_naturality_right, Category.assoc,
    ← relativeFunctorUncurry_naturality, Category.comp_id]

/-- 相対切断を全切断表示に戻して評価すると、元の相対評価そのもの。 -/
lemma simplicialSectionsRelativeIso_inv_evaluation {E B T : SSet.{u}}
    (p : E ⟶ B) (k : T ⟶ relativeFunctorSpace p (𝟙 B)) :
    (B ◁ (k ≫ (HomotopyLimits.simplicialSectionsRelativeIso p).inv)) ≫
      HomotopyLimits.simplicialSectionsEvaluation p = relativeFunctorUncurry k := by
  rw [whiskerLeft_comp, Category.assoc]
  dsimp only [HomotopyLimits.simplicialSectionsRelativeIso]
  rw [HomotopyLimits.simplicialSectionsLift_evaluation]
  exact (relativeFunctorUncurry_naturality k (𝟙 _)).symm

end SerrePositivity.InfinityCategories
