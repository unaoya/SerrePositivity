module
public import SerrePositivity.KST.SConstruction.BoundaryPointedComparison
public import SerrePositivity.KST.SConstruction.PointedPostcomposition

/-! # 従来の K 空間と全零境界商模型の比較
概要：零対象を選んだ従来の K 空間から、自然な基点を持つ K 空間へ全基点 π_* 同型を構成する。
方針：一重 S の多単体模型との厳密な一致と零段の商の比較を使う。
規約：delooping やスペクトルの Ω 条件はここでは主張しない。使われ方：K の自然性の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel
open scoped Simplicial

/-- 概要：全零方向の境界を潰した K 空間の関手。
方針：点つき Kan 実現へ L9 の Ω 関手を適用する。
規約：選択した零対象の保存は不要。使われ方：K の自然な模型。 -/
def boundaryKSpaceFunctor : StableModel.{u} ⥤ PointedSimplicialSet.{u} :=
  boundaryKanRealizationFunctor 0 ⋙
    PointedObject.basedHomFunctor (C := SSet.{u}) PointedSimplicialSet.circle.{u}

/-- 概要：全零境界の商から作る K 空間は Kan。
方針：Kan 実現の loop の Kan 性。
規約：全ての安定な入力。使われ方：ホモトピー群の比較。 -/
instance boundaryKSpaceFunctor_kanComplex (X : StableModel.{u}) :
    KanComplex ((boundaryKSpaceFunctor.obj X).right) := Spectra.loopSpace_kanComplex _

/-- 概要：従来の実現から全零境界を潰す実現への点つき比較。
方針：従来の零図式を基点とする任意頂点の比較を使う。
規約：元の実現の定義を変更しない。使われ方：旧 K 空間との比較。 -/
def boundarySRealizationComparison (X : StableModel.{u}) :
    pointedSRealization X.carrier ⟶ (boundaryReducedRealizationFunctor 0).obj X :=
  boundaryReductionPointedMap 0 X
    (coreSConstructionZeroVertex 0 (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.chosenZeroVertex X.carrier).vertex
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.chosenZeroVertex X.carrier).isZero)

/-- 概要：実現の点つき比較は Kan 置換後に全基点 π_* 同型。
方針：商写像の局所化可逆性と L9 への接続を使う。
規約：旧実現の Kan 性は仮定しない。使われ方：K 空間の比較。 -/
lemma boundarySRealizationComparison_kan_piIsomorphism (X : StableModel.{u}) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (Spectra.PointedKanReplacement.map (boundarySRealizationComparison X)).right := by
  apply pointedKanReplacement_map_piIsomorphism_of_localized_isIso
  exact boundaryReductionQuotient_image_isIso AnodyneHomotopy.anodyneQ
    (Localization.inverts AnodyneHomotopy.anodyneQ anodyneExtensions) 0 X

/-- 概要：従来の K 空間から選択なしの K 空間への写像。
方針：実現の比較を Kan 置換して L9 の Ω を適用する。
規約：元の kSpace の定義を変更しない。使われ方：自然な関手模型との照合。 -/
def kSpaceBoundaryComparison (X : StableModel.{u}) :
    kSpace X.carrier ⟶ boundaryKSpaceFunctor.obj X :=
  (PointedObject.basedHomFunctor (C := SSet.{u}) PointedSimplicialSet.circle.{u}).map
    (Spectra.PointedKanReplacement.map (boundarySRealizationComparison X))

/-- 概要：従来の K 空間と選択なしの K 空間の比較は全基点 π_* 同型。
方針：Kan な実現の比較の π_* 同型を L9 の点つき写像空間へ移す。
規約：全自然数次数と全基点を含む。使われ方：K の零対象の選択によらない自然性。 -/
lemma kSpaceBoundaryComparison_piIsomorphism (X : StableModel.{u}) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (kSpaceBoundaryComparison X).right :=
  Spectra.PointedMapping.post_piIsomorphism PointedSimplicialSet.circle
    (Spectra.PointedKanReplacement.map (boundarySRealizationComparison X))
    (boundarySRealizationComparison_kan_piIsomorphism X)

/-- 概要：実現の比較は既存の基点を保つ後合成と可換。
方針：自然な商写像の自然性を底の単体集合で照合する。
規約：元の chosen zero 保存条件を明示する。使われ方：既存の自然性との接続。 -/
lemma boundarySRealizationComparison_naturality {X Y : StableModel.{u}}
    (f : X.carrier ⟶ Y.carrier) (hf : PreservesSConstructionData f) (hz : PreservesChosenZero f) :
    pointedSPostcomp f hf hz ≫ boundarySRealizationComparison Y =
      boundarySRealizationComparison X ≫ (boundaryReducedRealizationFunctor 0).map
        (⟨f, PreservesSConstructionData.toCofiberData hf⟩ : X ⟶ Y) := by
  apply Under.UnderMorphism.ext
  exact (boundaryReductionNat 0).naturality
    (⟨f, PreservesSConstructionData.toCofiberData hf⟩ : X ⟶ Y)

/-- 概要：K 空間の比較は既存の基点を保つ後合成と可換。
方針：実現の比較の自然性へ Kan 置換・Ω の関手を適用する。
規約：標的の新しい K 空間の関手自体は chosen zero 保存を要求しない。
使われ方：従来の API と自然な K 関手の照合。 -/
lemma kSpaceBoundaryComparison_naturality {X Y : StableModel.{u}}
    (f : X.carrier ⟶ Y.carrier) (hf : PreservesSConstructionData f) (hz : PreservesChosenZero f) :
    kSpacePostcomp f hf hz ≫ kSpaceBoundaryComparison Y =
      kSpaceBoundaryComparison X ≫ boundaryKSpaceFunctor.map
        (⟨f, PreservesSConstructionData.toCofiberData hf⟩ : X ⟶ Y) := by
  let F := Spectra.PointedKanReplacement.functor ⋙
    PointedObject.basedHomFunctor (C := SSet.{u}) PointedSimplicialSet.circle.{u}
  change F.map (pointedSPostcomp f hf hz) ≫ F.map (boundarySRealizationComparison Y) =
    F.map (boundarySRealizationComparison X) ≫ F.map ((boundaryReducedRealizationFunctor 0).map
      (⟨f, PreservesSConstructionData.toCofiberData hf⟩ : X ⟶ Y))
  rw [← F.map_comp, ← F.map_comp, boundarySRealizationComparison_naturality f hf hz]

end SerrePositivity.KST.SConstruction
