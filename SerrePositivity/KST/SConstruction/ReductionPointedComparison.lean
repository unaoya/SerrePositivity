module
public import SerrePositivity.KST.SConstruction.ReductionEquivalence
public import SerrePositivity.KST.SConstruction.LocalizedPiComparison
public import SerrePositivity.KST.SConstruction.KSpace
public import SerrePositivity.KST.Spectra.PostMappingIsomorphism

/-! # 零頂点を選んだ実現から自然な商への点つき比較
概要：零段の任意の頂点を基点とした実現は零段全体を潰す商へ自然に写る。
方針：cofiber の条件で基点を保ち、Kan 置換後の全基点 π_* 同型へ接続する。
規約：比較射は選べる全零頂点に対して作る。使われ方：旧 K 空間と自然な K 空間の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel
open scoped Simplicial

local instance (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] :
    KanComplex (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).right := Spectra.loopSpace_kanComplex Y

/-- 概要：零段の任意の頂点を選んだ点つき対角から、零段を潰す商への点つき写像。
方針：頂点の定値射と cofiber の関係式を合成する。
規約：選んだ頂点の像は商の基点。使われ方：従来の零対象基点の比較。 -/
def diagonalReductionPointedMap (X : SimplexCategoryᵒᵖ ⥤ SSet.{u})
    (z : (X.obj (Opposite.op ⦋0⦌)) _⦋0⦌) :
    PointedSimplicialSet.ofVertex (simplicialDiagonalFunctor.obj X)
      ((diagonalZeroColumn X).app (Opposite.op ⦋0⦌) z) ⟶ reducedDiagonal X :=
  Under.homMk (diagonalReductionQuotient X) (by
    change SSet.const ((diagonalZeroColumn X).app (Opposite.op ⦋0⦌) z) ≫
      diagonalReductionQuotient X = (reducedDiagonal X).hom
    rw [← SSet.const_comp z (diagonalZeroColumn X), Category.assoc]
    change SSet.const z ≫ (diagonalZeroColumn X ≫
      PointedObject.cofiberQuotient (diagonalZeroColumn X)) = _
    rw [PointedObject.cofiberQuotient_condition, comp_toUnit_assoc, toUnit_unit, Category.id_comp]
    rfl)

/-- 概要：可縮零段の商への点つき比較は Kan 置換後に全基点 π_* 同型。
方針：商写像の局所化可逆性を L9 の実際の π_* 比較へ渡す。
規約：元の対角の Kan 性は不要。使われ方：選んだ零対象の実現模型との比較。 -/
lemma diagonalReductionPointedMap_kan_piIsomorphism (X : SimplexCategoryᵒᵖ ⥤ SSet.{u})
    (hX : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (X.obj (Opposite.op ⦋0⦌)))
    (z : (X.obj (Opposite.op ⦋0⦌)) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (Spectra.PointedKanReplacement.map (diagonalReductionPointedMap X z)).right := by
  apply pointedKanReplacement_map_piIsomorphism_of_localized_isIso
  exact diagonalReductionQuotient_image_isIso AnodyneHomotopy.anodyneQ
    (Localization.inverts AnodyneHomotopy.anodyneQ anodyneExtensions) X hX

/-- 概要：零段を選んだ実現の Ω から自然な商の Ω への写像。
方針：点つき比較を Kan 置換し、円からの点つき内部 Hom を適用する。
規約：Ω は L9 の既存の模型。使われ方：K 空間の比較。 -/
def diagonalReductionLoopMap (X : SimplexCategoryᵒᵖ ⥤ SSet.{u})
    (z : (X.obj (Opposite.op ⦋0⦌)) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (Spectra.PointedKanReplacement.obj
      (PointedSimplicialSet.ofVertex (simplicialDiagonalFunctor.obj X)
        ((diagonalZeroColumn X).app (Opposite.op ⦋0⦌) z))) ⟶
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (Spectra.PointedKanReplacement.obj (reducedDiagonal X)) :=
  (PointedObject.basedHomFunctor (C := SSet.{u}) PointedSimplicialSet.circle.{u}).map
    (Spectra.PointedKanReplacement.map (diagonalReductionPointedMap X z))

/-- 概要：可縮零段を潰す比較は Ω 後も全基点 π_* 同型。
方針：Kan な点つき対象間の π_* 同型を L9 の点つき内部 Hom へ移す。
規約：零次数を含む。使われ方：K 空間の選択によらない模型の比較。 -/
lemma diagonalReductionLoopMap_piIsomorphism (X : SimplexCategoryᵒᵖ ⥤ SSet.{u})
    (hX : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (X.obj (Opposite.op ⦋0⦌)))
    (z : (X.obj (Opposite.op ⦋0⦌)) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (diagonalReductionLoopMap X z).right :=
  Spectra.PointedMapping.post_piIsomorphism PointedSimplicialSet.circle
    (Spectra.PointedKanReplacement.map (diagonalReductionPointedMap X z))
    (diagonalReductionPointedMap_kan_piIsomorphism X hX z)

end SerrePositivity.KST.SConstruction
