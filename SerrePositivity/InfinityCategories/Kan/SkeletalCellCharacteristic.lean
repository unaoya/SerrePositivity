module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Kan.SkeletalAttachmentPushout

/-!
概要：骨格のセルの付着写像と特徴射を元の単体の Yoneda 射へ比較する。
方針：相対セル分解の余積の標準射と骨格の同型の計算を展開する。
規約：d は追加するセルの実際の次元。
使われ方：Goerss–Jardine VIII §1。セルごとの境界充填を骨格へ貼り合わせる。
-/

@[expose] public section

universe u
open CategoryTheory Limits SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra.SkeletalCellAttachment
end SerrePositivity.KST.Spectra.SkeletalCellAttachment
namespace SerrePositivity.InfinityCategories.Kan.SkeletalCellAttachment
open SerrePositivity.KST.Spectra.SkeletalCellAttachment

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：各セルの付着写像を全体へ含めると元の単体の境界の射になる。
方針：余積と骨格の同型と部分複体の lift の標準射を計算する。
規約：元のセルの単体は c.simplex。
使われ方：Goerss–Jardine VIII §1。付着境界の面の具体化。 -/
@[reassoc (attr := simp)]
theorem cell_attachingMap_ι (K : SSet.{u}) (d : ℕ)
    (c : relativeCellComplexOfMono.Cell (K.skeleton d).ι d) :
    c.ιSigmaBoundary ≫ attachingMap K d ≫ (K.skeleton d).ι =
      (boundary d).ι ≫ yonedaEquiv.symm c.simplex := by
  simp [attachingMap, Subcomplex.eqToIso]

/-- 概要：各セルの特徴射を全体へ含めると元の単体の Yoneda 射になる。
方針：余積と骨格の同型と部分複体の lift の標準射を計算する。
規約：特徴射の標的は次元 d のセルを含む骨格。
使われ方：Goerss–Jardine VIII §1。既存の延長からセルの充填を取り出す。 -/
@[reassoc (attr := simp)]
theorem cell_characteristicMap_ι (K : SSet.{u}) (d : ℕ)
    (c : relativeCellComplexOfMono.Cell (K.skeleton d).ι d) :
    c.ιSigmaStdSimplex ≫ characteristicMap K d ≫ (K.skeleton (d + 1)).ι =
      yonedaEquiv.symm c.simplex := by
  simp [characteristicMap, Subcomplex.eqToIso]

end

end SerrePositivity.InfinityCategories.Kan.SkeletalCellAttachment

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SkeletalCellAttachment.cell_attachingMap_ι := _root_.SerrePositivity.InfinityCategories.Kan.SkeletalCellAttachment.cell_attachingMap_ι

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SkeletalCellAttachment.cell_attachingMap_ι_assoc := _root_.SerrePositivity.InfinityCategories.Kan.SkeletalCellAttachment.cell_attachingMap_ι_assoc

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SkeletalCellAttachment.cell_characteristicMap_ι := _root_.SerrePositivity.InfinityCategories.Kan.SkeletalCellAttachment.cell_characteristicMap_ι

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SkeletalCellAttachment.cell_characteristicMap_ι_assoc := _root_.SerrePositivity.InfinityCategories.Kan.SkeletalCellAttachment.cell_characteristicMap_ι_assoc
