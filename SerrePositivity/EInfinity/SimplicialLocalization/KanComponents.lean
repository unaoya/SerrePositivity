module

public import SerrePositivity.EInfinity.SimplicialLocalization.ComponentsEquivalence
public import SerrePositivity.EInfinity.SimplicialLocalization.KanEnrichment
public import SerrePositivity.HomotopicalAlgebra.Simplicial.PiZeroLocalization

/-!
# Kan 化した DK Hom の連結成分と普通の局所化

概要：同じ Ex∞ の単位を通して実際の Kan Hom の π₀ を普通の局所化と同定する。
方針：元の単位の anodyne 性から π₀ の全単射を取り、元の augmentation の同値と合成する。
規約：単体集合のモデル構造や元の Hom の Kan 性を入力しない。
使われ方：CAlg_R の構成に使う Kan Hom と元の Map^h の零次比較。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.SimplicialLocalization

open CategoryTheory


variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})

/-- 概要：同じ Kan 化の単位は元の Hom の π₀ の同値を誘導する（Dwyer–Kan）。
方針：元の anodyne 単位の実際の連結成分の全単射を使う。
規約：単体集合のモデル構造は要求しない。
使われ方：Kan 化前後の零次の同定。 -/
def localizationHomKanUnitPiZeroEquiv (X Y : C.category) :
    SSet.π₀ (localizationHom C X Y) ≃ SSet.π₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj (localizationHom C X Y)) := by
  let L := SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ
  have h : IsIso (L.map (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app (localizationHom C X Y))) :=
    Localization.inverts L SSet.anodyneExtensions _ (localizationHomKanUnit_anodyne C X Y)
  exact Equiv.ofBijective (SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app (localizationHom C X Y)))
    (SerrePositivity.SimplicialModel.PiZeroLocalization.piZero_bijective _ h)

/-- 概要：実際の Kan Hom の π₀ は元の普通の局所化 Hom（Dwyer–Kan）。
方針：同じ単位の π₀ 同値の逆と元の augmentation の同値を合成する。
規約：元の Kan 化・比較射・局所化を保持する。
使われ方：CAlg_R の Kan Hom の零次比較。 -/
def kanLocalizationHomPiZeroEquiv (X Y : C.category) :
    SSet.π₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj (localizationHom C X Y)) ≃
      (C.weakEquivalences.Q.obj X ⟶ C.weakEquivalences.Q.obj Y) :=
  (localizationHomKanUnitPiZeroEquiv C X Y).symm.trans (localizationHomPiZeroEquiv C X Y)

/-- 概要：Kan 化の単位を通した元の射の類は同じ Q の像（Dwyer–Kan）。
方針：同じ単位の順逆則と元の augmentation の生成射の正規化を使う。
規約：元の射・単位・零単体の類を保持する。
使われ方：既存の Map^h と Kan Hom の零次の照合。 -/
lemma kanLocalizationHomPiZeroEquiv_arrow {X Y : C.category} (f : X ⟶ Y) :
    kanLocalizationHomPiZeroEquiv C X Y
        (SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app (localizationHom C X Y)) (localizationArrowClass C f)) =
      C.weakEquivalences.Q.map f := by
  change localizationHomPiZeroEquiv C X Y
    ((localizationHomKanUnitPiZeroEquiv C X Y).symm
      ((localizationHomKanUnitPiZeroEquiv C X Y) (localizationArrowClass C f))) = _
  rw [Equiv.symm_apply_apply, localizationHomPiZeroEquiv_arrow]

end SerrePositivity.EInfinity.SimplicialLocalization
