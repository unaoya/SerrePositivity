module

public import SerrePositivity.EInfinity.SimplicialLocalization.Enrichment
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.ExInfinityMonoidal

/-!
# Ex∞ による単体的局所化の Hom の Kan 化

概要：Dwyer–Kan の厳密な単体的局所化の Hom を同じ有限積保存 Ex∞ で Kan 化する。
方針：実際の monoidal 関手で豊穣構造を移し、元の単位の monoidal 性を使う。
規約：単体集合のモデル構造を入力せず、元の豊穣合成を保持する。
使われ方：局所 Kan な単体的圏の coherent nerve。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.SimplicialLocalization

open CategoryTheory MonoidalCategory


/-- 概要：同じ Ex∞ で豊穣 Hom を Kan 化した対象の型（Dwyer–Kan）。
方針：元の対象の豊穣構造を有限積保存 Ex∞ で移す。
規約：対象を変更せず、Hom だけを同じ functor で移す。
使われ方：Kan な単体的局所化の構成。 -/
abbrev KanLocalizationObjects (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) :=
  TransportEnrichment _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.{u} (LocalizationObjects C)

/-- 概要：Kan 化した Hom を持つ標準的な基礎の単体的圏（Dwyer–Kan）。
方針：移した豊穣構造へ ForgetEnrichment を適用する。
規約：合成・単位は元の構造を同じ monoidal 関手で移したもの。
使われ方：coherent nerve の局所 Kan な入力。 -/
abbrev KanLocalizationCategory (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) :=
  ForgetEnrichment SSet.{u} (KanLocalizationObjects C)

/-- 概要：Kan 化した局所化の Hom は同じ Ex∞ の値（Dwyer–Kan）。
方針：豊穣構造の移送と ForgetEnrichment の定義を評価する。
規約：元の Hom の全単体を Ex∞ の単位で比較する。
使われ方：Kan 性と Hom の比較の照合。 -/
lemma kanLocalizationCategory_sHom (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y : KanLocalizationCategory C) :
    SimplicialCategory.sHom X Y = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj (localizationHom C X Y) := rfl

/-- 概要：Kan 化した単体的局所化の全 Hom は Kan 複体（Dwyer–Kan）。
方針：実際の Ex∞ の Kan 性を使う。
規約：元の Hom の Kan 性や単体集合モデルの入力仮定は不要。
使われ方：coherent nerve の quasicategory 性。 -/
instance kanLocalizationHom_kanComplex (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})
    (X Y : KanLocalizationCategory C) : SSet.KanComplex (SimplicialCategory.sHom X Y) := by
  change SSet.KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj (localizationHom C X Y))
  infer_instance

/-- 概要：元の局所化 Hom から Kan 化した Hom への同じ anodyne 比較（Dwyer–Kan）。
方針：元の Ex∞ の単位の anodyne 性を使う。
規約：新しい弱同値や写像空間を選ばない。
使われ方：単体的局所化と元の Hom のホモトピー型の比較。 -/
lemma localizationHomKanUnit_anodyne (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y : C.category) :
    SSet.anodyneExtensions (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app (localizationHom C X Y)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit_anodyne _

/-- 概要：Ex∞ の同じ単位は厳密な豊穣関手を与える（Dwyer–Kan）。
方針：元の単位の自然性・monoidal な単位則と合成則を使う。
規約：元の対象・元の合成・元の Hom の単位を保持する。
使われ方：Kan 化の前後の単体的局所化の比較。 -/
def kanLocalizationUnit (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) :
    EnrichedFunctor SSet.{u} (LocalizationObjects C) (KanLocalizationObjects C) where
  obj X := X
  map X Y := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app (localizationHom C X Y)
  map_id X := by
    change localizationIdentity C X ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app (localizationHom C X X) =
      Functor.LaxMonoidal.ε _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (localizationIdentity C X)
    have h := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.naturality (localizationIdentity C X)
    have hu : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app (𝟙_ SSet.{u}) = Functor.LaxMonoidal.ε _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity := by
      simpa using (NatTrans.IsMonoidal.unit (τ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.{u}))
    exact h.trans (congrArg (fun z => z ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (localizationIdentity C X)) hu)
  map_comp X Y Z := by
    change localizationComposition C X Y Z ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app (localizationHom C X Z) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app (localizationHom C X Y) ⊗ₘ
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app (localizationHom C Y Z)) ≫
          Functor.LaxMonoidal.μ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity _ _ ≫
            _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (localizationComposition C X Y Z)
    have h := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.naturality (localizationComposition C X Y Z)
    have hμ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app (localizationHom C X Y ⊗ localizationHom C Y Z) =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app (localizationHom C X Y) ⊗ₘ
          _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app (localizationHom C Y Z)) ≫
            Functor.LaxMonoidal.μ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity _ _ := by
      simpa using (NatTrans.IsMonoidal.tensor (τ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.{u})
        (X := localizationHom C X Y) (Y := localizationHom C Y Z))
    exact h.trans ((congrArg (fun z => z ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (localizationComposition C X Y Z)) hμ).trans (Category.assoc _ _ _))

/-- 概要：同じ豊穣単位は基礎の単体的圏の関手を与える（Dwyer–Kan）。
方針：構成済みの豊穣関手を ForgetEnrichment で送る。
規約：元の単位・合成の保存を保持する。
使われ方：coherent nerve の前後の比較。 -/
def kanLocalizationUnitFunctor (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) :
    LocalizationCategory C ⥤ KanLocalizationCategory C :=
  (kanLocalizationUnit C).forget

end SerrePositivity.EInfinity.SimplicialLocalization
