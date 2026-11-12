module
public import SerrePositivity.KST.SConstruction.PointedCoreSimplicial
public import SerrePositivity.KST.Spectra.PointedKanReplacement
public import SerrePositivity.KST.Spectra.SuspensionLoop

/-! # 対角実現の loop としての K 空間
概要：ιS•C の対角に零図式の基点を取り、Kan 置換後の Ω を構成する。
方針：L9 の点つき Kan 置換と loopSpace を使う。
規約：BGT §7。反復 S• の delooping とスペクトルの Ω 条件は別に証明する。
使われ方：連結 K 理論の空間模型。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：零図式を基点とする単体的 core の対角実現。
方針：S_0 の零図式の頂点で点つき単体集合を作る。
規約：零対象の選択は HasZeroVertex の既存の選択。使われ方：K 空間の loop の入力。 -/
def pointedSRealization (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex C] :
    PointedSimplicialSet.{u} :=
  PointedSimplicialSet.ofVertex (diagonalCoreSConstruction C)
    (coreSConstructionZeroVertex 0 (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.chosenZeroVertex C).vertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.chosenZeroVertex C).isZero)

/-- 概要：対角実現の点つき Kan 置換。
方針：L9 の点つき小対象論法の置換を適用する。
規約：対角自体の Kan 性を仮定しない。使われ方：loop が Kan となる実現模型。 -/
def kanSRealization (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex C] :
    PointedSimplicialSet.{u} := Spectra.PointedKanReplacement.obj (pointedSRealization C)

/-- 概要：置換した実現は Kan 複体。
方針：L9 の置換の Kan 性を使う。
規約：全ての零対象を持つ quasicategory。使われ方：K 空間の Kan 性。 -/
instance kanSRealization_kanComplex (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex C] :
    KanComplex (kanSRealization C).right := Spectra.PointedKanReplacement.obj_kanComplex _

/-- 概要：対角実現から Kan 置換への点つき比較射。
方針：L9 の置換の自然な単位を使う。
規約：基点を厳密に保つ。使われ方：実現模型と fibrant 模型の比較。 -/
def sRealizationToKan (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex C] :
    pointedSRealization C ⟶ kanSRealization C := Spectra.PointedKanReplacement.unit.app _

/-- 概要：実現の Kan 置換の単位は anodyne。
方針：L9 の置換の単位の充填性を使う。
規約：モデル構造の弱同値を入力にしない。使われ方：実現模型の比較。 -/
lemma sRealizationToKan_anodyne (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex C] :
    anodyneExtensions (sRealizationToKan C).right := Spectra.PointedKanReplacement.unit_anodyne _

/-- 概要：K 空間を単体的 core の実現の loop と定義する。
方針：Kan 置換した実現に L9 の円からの点つき内部 Hom を適用する。
規約：K(C)=Ω|ιS•C|。使われ方：連結スペクトルの零空間と π₀ の比較。 -/
def kSpace (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex C] : PointedSimplicialSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (kanSRealization C)

/-- 概要：K 空間は Kan 複体。
方針：置換の Kan 性と L9 の loop の Kan 性を使う。
規約：安定性は後続の K 理論の定理に使う。使われ方：π_n と BF 模型の入力。 -/
instance kSpace_kanComplex (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex C] :
    KanComplex (kSpace C).right := Spectra.loopSpace_kanComplex _

end SerrePositivity.KST.SConstruction
