module

public import SerrePositivity.KST.Spectra.UnderlyingWeightedCochains

/-!
概要：通常の cochain の係数への関手性と点つき忘却の比較の自然性。
方針：重みの前合成と係数の後合成を end の各射影で交換する。
規約：任意の単体的な重みと通常の係数図式に対する構成。
使われ方：Goerss–Jardine VIII §§1–2。Tot と end の係数への自然な比較。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed SSet Opposite


namespace SerrePositivity.KST.Spectra.UnderlyingWeightedCochains

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {I : Type u} [SmallCategory I]

lemma map_pre {W V : I ⥤ SSet.{u}} (θ : W ⟶ V) {H E : I ⥤ SSet.{u}} (τ : H ⟶ E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap V τ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre θ E =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre θ H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap W τ := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections_hom_ext
  intro i
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre_π, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap_π,
    Category.assoc]
  conv_rhs => rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap_π, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre_π, Category.assoc]
  rw [pre_comm_ihom_map]

/-- 概要：通常の係数図式の射を余単体 cochain の射へ送る。
方針：各次数で係数の end の後合成を行う。
規約：構造射との可換性は end の二変数の可換式。
使われ方：Goerss–Jardine VIII §§1–2。通常の Tot の係数の射への作用。 -/
def map (W : SimplicialObject (I ⥤ SSet.{u})) {H E : I ⥤ SSet.{u}} (τ : H ⟶ E) :
    obj W H ⟶ obj W E where
  app n := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap (W.obj (op n)) τ
  naturality _ _ f := (map_pre (W.map f.op) τ).symm

lemma pointedUnderlyingIso_natural (W : SimplicialObject (I ⥤ SSet.{u}))
    {D E : I ⥤ PointedSimplicialSet.{u}} (τ : D ⟶ E) :
    Functor.whiskerRight (weightedCochainsMap W τ) PointedSimplicialSet.forget ≫
        (pointedUnderlyingIso W E).hom =
      (pointedUnderlyingIso W D).hom ≫
        map W (Functor.whiskerRight τ PointedSimplicialSet.forget) := by
  apply NatTrans.ext
  funext n
  exact PointedWeightedEnd.underlyingIso_natural (W.obj (op n)) τ

end

end SerrePositivity.KST.Spectra.UnderlyingWeightedCochains
