module

public import SerrePositivity.KST.Spectra.CochainDensityParameter
public import SerrePositivity.KST.Spectra.TotalizationFunctor

/-!
概要：単体ごとの離散重みの cochain の通常の Tot と完全な重みの end の実際の同型。
方針：パラメーターに自然な Hom の同値を Yoneda の完全忠実性で戻す。
規約：Kan 性も Reedy 置換も仮定しない厳密な単体集合の同型。
使われ方：Goerss–Jardine VIII §1、式 (1.1)。群 cochain の Tot と EG の end の模型比較。
-/

@[expose] public section

universe u

open CategoryTheory SSet


namespace SerrePositivity.KST.Spectra.SimplexDensity

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {I : Type u} [SmallCategory I]

/-- 概要：離散的単体の cochain の通常の Tot は完全な重みの end と同型。
方針：標準単体の密度から得られた Hom の自然な同値を Yoneda で戻す。
規約：単体集合の実際の同型であり導来極限性の主張は含まない。
使われ方：Goerss–Jardine VIII §1、式 (1.1)。通常の Tot の end としての計算。 -/
def totalizationEndIso (W H : I ⥤ SSet.{u}) :
    CosimplicialTotalization.obj (UnderlyingWeightedCochains.obj (discreteLevels W) H) ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections W H :=
  Yoneda.fullyFaithful.preimageIso
    (NatIso.ofComponents (fun A ↦ (totalizationEndHomEquiv W H A.unop).toIso)
      (fun f ↦ by
        ext s
        exact totalizationEndHomEquiv_pre W H f.unop s))

lemma totalizationEndIso_hom (W H : I ⥤ SSet.{u}) :
    (totalizationEndIso W H).hom = totalizationEndHomEquiv W H _ (𝟙 _) := rfl

lemma totalizationEndHomEquiv_apply (W H : I ⥤ SSet.{u}) {A : SSet.{u}}
    (s : A ⟶ CosimplicialTotalization.obj
      (UnderlyingWeightedCochains.obj (discreteLevels W) H)) :
    totalizationEndHomEquiv W H A s = s ≫ (totalizationEndIso W H).hom := by
  rw [totalizationEndIso_hom, ← totalizationEndHomEquiv_pre, Category.comp_id]

/-- 概要：点つき cochain の通常の Tot の基礎は点つき end の基礎と同型。
方針：cochain の忘却の比較、通常の密度の同型、end の忘却の比較を合成する。
規約：この宣言は基礎単体集合の同型であり基点の保存は別に扱う。
使われ方：Goerss–Jardine VIII §1、HA §1.4.2。点つき密度比較の入力。 -/
def pointedUnderlyingTotalizationEndIso (W : I ⥤ SSet.{u})
    (D : I ⥤ PointedSimplicialSet.{u}) :
    (PointedTotalization.obj (weightedCochains (discreteLevels W) D)).right ≅
      (PointedWeightedEnd.obj W D).right :=
  CosimplicialTotalization.functor.mapIso
      (UnderlyingWeightedCochains.pointedUnderlyingIso (discreteLevels W) D) ≪≫
    totalizationEndIso W (D ⋙ PointedSimplicialSet.forget) ≪≫
      (PointedWeightedEnd.underlyingIso W D).symm

end

end SerrePositivity.KST.Spectra.SimplexDensity
