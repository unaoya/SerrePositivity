module
public import SerrePositivity.KST.SConstruction.ReducedMultiRealization
public import SerrePositivity.KST.SConstruction.ReductionPointedComparison
public import SerrePositivity.KST.SConstruction.PointedPostcomposition

/-! # 従来の K 空間と選択なしの K 空間の比較
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

/-- 概要：一重 S の対角図式は従来の単体的 core と一致する。
方針：自己関手の零回反復と合成の定義を計算する。
規約：対象・全構造射の厳密な等号。使われ方：旧実現との比較。 -/
lemma multiDiagonalDiagramFunctor_one_obj (X : StableModel.{u}) :
    (multiDiagonalDiagramFunctor 1).obj X = simplicialCoreSConstruction X.carrier := rfl

/-- 概要：従来の零対象基点を持つ実現から自然な基点を持つ実現への点つき比較。
方針：零段の任意の頂点の比較に選んだ零図式を入れる。
規約：標的は零対象の選択に依存しない。使われ方：K 空間の比較射の入力。 -/
def reducedSRealizationComparison (X : StableModel.{u}) :
    pointedSRealization X.carrier ⟶ (reducedMultiRealizationFunctor 0).obj X :=
  Under.homMk ((multiRealizationReductionNat 0).app X) (by
    have h := Under.w (diagonalReductionPointedMap (simplicialCoreSConstruction X.carrier)
      (coreSConstructionZeroVertex 0 (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex X.carrier).vertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex X.carrier).isZero))
    change (PointedSimplicialSet.ofVertex
      (simplicialDiagonalFunctor.obj (simplicialCoreSConstruction X.carrier))
      ((diagonalZeroColumn (simplicialCoreSConstruction X.carrier)).app (Opposite.op ⦋0⦌)
        (coreSConstructionZeroVertex 0 (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex X.carrier).vertex
          (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex X.carrier).isZero))).hom ≫
        diagonalReductionQuotient (simplicialCoreSConstruction X.carrier) =
          (reducedDiagonal (simplicialCoreSConstruction X.carrier)).hom at h
    rw [diagonalZeroColumn_zero] at h
    exact h)

/-- 概要：実現の点つき比較は Kan 置換後に全基点 π_* 同型。
方針：商写像の局所化可逆性と L9 への接続を使う。
規約：旧実現の Kan 性は仮定しない。使われ方：K 空間の比較。 -/
lemma reducedSRealizationComparison_kan_piIsomorphism (X : StableModel.{u}) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (Spectra.PointedKanReplacement.map (reducedSRealizationComparison X)).right := by
  apply pointedKanReplacement_map_piIsomorphism_of_localized_isIso
  exact multiRealizationReduction_image_isIso AnodyneHomotopy.anodyneQ
    (Localization.inverts AnodyneHomotopy.anodyneQ anodyneExtensions) 0 X

/-- 概要：従来の K 空間から選択なしの K 空間への写像。
方針：実現の比較を Kan 置換して L9 の Ω を適用する。
規約：元の kSpace の定義を変更しない。使われ方：自然な関手模型との照合。 -/
def kSpaceReductionComparison (X : StableModel.{u}) :
    kSpace X.carrier ⟶ reducedKSpaceFunctor.obj X :=
  (PointedObject.basedHomFunctor (C := SSet.{u}) PointedSimplicialSet.circle.{u}).map
    (Spectra.PointedKanReplacement.map (reducedSRealizationComparison X))

/-- 概要：従来の K 空間と選択なしの K 空間の比較は全基点 π_* 同型。
方針：Kan な実現の比較の π_* 同型を L9 の点つき写像空間へ移す。
規約：全自然数次数と全基点を含む。使われ方：K の零対象の選択によらない自然性。 -/
lemma kSpaceReductionComparison_piIsomorphism (X : StableModel.{u}) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (kSpaceReductionComparison X).right :=
  Spectra.PointedMapping.post_piIsomorphism PointedSimplicialSet.circle
    (Spectra.PointedKanReplacement.map (reducedSRealizationComparison X))
    (reducedSRealizationComparison_kan_piIsomorphism X)

/-- 概要：実現の比較は既存の基点を保つ後合成と可換。
方針：自然な商写像の自然性を底の単体集合で照合する。
規約：元の chosen zero 保存条件を明示する。使われ方：既存の自然性との接続。 -/
lemma reducedSRealizationComparison_naturality {X Y : StableModel.{u}}
    (f : X.carrier ⟶ Y.carrier) (hf : PreservesSConstructionData f) (hz : PreservesChosenZero f) :
    pointedSPostcomp f hf hz ≫ reducedSRealizationComparison Y =
      reducedSRealizationComparison X ≫ (reducedMultiRealizationFunctor 0).map
        (⟨f, PreservesSConstructionData.toCofiberData hf⟩ : X ⟶ Y) := by
  apply Under.UnderMorphism.ext
  exact (multiRealizationReductionNat 0).naturality
    (⟨f, PreservesSConstructionData.toCofiberData hf⟩ : X ⟶ Y)

/-- 概要：K 空間の比較は既存の基点を保つ後合成と可換。
方針：実現の比較の自然性へ Kan 置換・Ω の関手を適用する。
規約：標的の新しい K 空間の関手自体は chosen zero 保存を要求しない。
使われ方：従来の API と自然な K 関手の照合。 -/
lemma kSpaceReductionComparison_naturality {X Y : StableModel.{u}}
    (f : X.carrier ⟶ Y.carrier) (hf : PreservesSConstructionData f) (hz : PreservesChosenZero f) :
    kSpacePostcomp f hf hz ≫ kSpaceReductionComparison Y =
      kSpaceReductionComparison X ≫ reducedKSpaceFunctor.map
        (⟨f, PreservesSConstructionData.toCofiberData hf⟩ : X ⟶ Y) := by
  let F := Spectra.PointedKanReplacement.functor ⋙
    PointedObject.basedHomFunctor (C := SSet.{u}) PointedSimplicialSet.circle.{u}
  change F.map (pointedSPostcomp f hf hz) ≫ F.map (reducedSRealizationComparison Y) =
    F.map (reducedSRealizationComparison X) ≫ F.map ((reducedMultiRealizationFunctor 0).map
      (⟨f, PreservesSConstructionData.toCofiberData hf⟩ : X ⟶ Y))
  rw [← F.map_comp, ← F.map_comp, reducedSRealizationComparison_naturality f hf hz]

end SerrePositivity.KST.SConstruction
