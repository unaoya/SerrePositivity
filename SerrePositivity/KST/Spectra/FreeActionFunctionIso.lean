module

public import SerrePositivity.KST.Spectra.FreeActionFunctionPre
public import SerrePositivity.KST.Spectra.FunctionComplexIsoFormula
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedRestriction

/-!
概要：自由作用の end の関数複体表示と自由軌道の射による前合成の整合性。
方針：同変族を軌道代表に制限し、同変拡張と制限の両逆を使って座標式を得る。
規約：任意の係数の単体集合の作用について構成する。
使われ方：Goerss–Jardine VIII §2。群 cochain の顔写像を関数群へ送る比較。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed SSet


namespace SerrePositivity.KST.Spectra.FreeActionFamily

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {G : Type u} [Group G]

/-- 概要：自由作用の end は軌道の添字集合上の関数複体と同型。
方針：自由作用の内部 Hom 表示と離散内部 Hom の関数複体表示を合成する。
規約：添字集合と係数の Kan 性は仮定しない。
使われ方：Goerss–Jardine VIII §2。非斉次 cochain の単体集合としての表示。 -/
def functionIso (S : Type u) (B : Action SSet.{u} G) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections (weight S) (coefficients B) ≅ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.obj S B.V :=
  endIso S B ≪≫ _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.DiscreteInternalHom.iso S B.V

lemma comp_functionIso (S : Type u) (B : Action SSet.{u} G) {A : SSet.{u}}
    (t : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections (weight S) (coefficients B)) :
    t ≫ (functionIso S B).hom =
      _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.DiscreteInternalHom.toFunctions S B.V (restrict S B (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry t)) := by
  rw [functionIso, Iso.trans_hom, ← Category.assoc, comp_endIso,
    homEquiv_apply, DiscreteInternalHom.comp_iso, uncurry_curry]

lemma functionPre_restrict {S T : Type u}
    (θ : (Action.leftRegular G ⊗ Action.trivial G T) ⟶
      (Action.leftRegular G ⊗ Action.trivial G S)) (B : Action SSet.{u} G) {A : SSet.{u}}
    (t : weight S ⊗ (Functor.const (AsSmall.{u} (SingleObj G))).obj A ⟶ coefficients B) :
    _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.DiscreteInternalHom.toFunctions T B.V (restrict T B
        (((GroupActionCochains.actionWeightFunctor G).map θ ▷
          (Functor.const (AsSmall.{u} (SingleObj G))).obj A) ≫ t)) =
      _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.DiscreteInternalHom.toFunctions S B.V (restrict S B t) ≫ functionPre θ B := by
  conv_lhs => rw [← extend_restrict S B t]
  rfl

/-- 概要：自由作用の end の関数表示は軌道の射の前合成と具体的な座標式で可換。
方針：end の uncurry の前合成の式を同変族の代表への制限へ送る。
規約：単体集合の実際の射の等式。
使われ方：Goerss–Jardine VIII §2。cochain の顔・退化の座標表示への移送。 -/
lemma functionIso_pre {S T : Type u}
    (θ : (Action.leftRegular G ⊗ Action.trivial G T) ⟶
      (Action.leftRegular G ⊗ Action.trivial G S)) (B : Action SSet.{u} G) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre ((GroupActionCochains.actionWeightFunctor G).map θ) (coefficients B) ≫
        (functionIso T B).hom =
      (functionIso S B).hom ≫ functionPre θ B := by
  rw [comp_functionIso]
  have hu := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry_comp_pre
    ((GroupActionCochains.actionWeightFunctor G).map θ)
    (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections (weight S) (coefficients B)))
  simp only [Category.id_comp] at hu
  rw [hu, functionPre_restrict]
  have h := comp_functionIso S B (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections (weight S) (coefficients B)))
  simp only [Category.id_comp] at h
  rw [h]

end

end SerrePositivity.KST.Spectra.FreeActionFamily
