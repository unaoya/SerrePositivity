module

public import SerrePositivity.DifferentialGraded.Resolution.Cell

/-!
# 半自由な生成元添加のフィルトレーションと K-flat 性

概要：一般の dg 圏への生成元添加で Hom の K-flat 性を保つことを証明する。
方針：語長の随伴次数、次数別分裂、語長と添加段階の逐次余極限を使う。
規約：非有界な試験複体を含む complexKFlat を証明し、項別の平坦性に置き換えない。
使われ方：Drinfeld §13.4・Lemma 13.5・Thm 3.4、KST D4 の一般分解。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w

namespace SerrePositivity.KST.DerivedGeometry.DGResolution

open CategoryTheory Limits
open SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

section Attachment
variable (I : Type w) [Small.{u} I] (C : DGCellAttachment.Family A D I)

/--
概要：語長フィルトレーションの各有限段階は K-flat。
方針：零段階は固定長の直和、後続段階は次数別分裂短完全列で帰納する。
規約：指定された生成元の境界を持つ最終微分を使う。
使われ方：Drinfeld §13.4・Lemma 13.5 の半自由な生成元添加。
-/
theorem finiteLength_kFlat (hD : localHomKFlat A D) (n : ℕ) (x y : D) :
    complexKFlat A (C.lengthHom A D I n x y) := by
  induction n with
  | zero =>
      exact complexKFlat_of_iso A (asIso (C.lengthQuotient A D I 0 x y))
        (C.exactLengthHom_kFlat A D I hD 0 x y)
  | succ n ih =>
      exact complexKFlat_of_degreewiseSplit A (C.lengthShortComplex A D I n x y)
        (C.lengthSplitting A D I n x y) ih
        (C.exactLengthHom_kFlat A D I hD (n + 1) x y)

/--
概要：全有限語からなる添加後の Hom 複体は K-flat。
方針：語長フィルトレーションの網羅性と完全な逐次余極限を使う。
規約：新生成元の微分は語長を下げ、固定長の随伴次数では消える。
使われ方：Drinfeld §13.4・Lemma 13.5 の添加段階に関する帰納。
-/
theorem attachment_kFlat (hD : localHomKFlat A D) (x y : D) :
    complexKFlat A (C.attachedHom A D I x y) := by
  have : AB5OfSize.{0, 0} (ModuleCat.{u} A) := AB5OfSize_of_univLE (ModuleCat.{u} A)
  have h := complexKFlat_colimit A (C.lengthDiagram A D I x y)
    (fun n => finiteLength_kFlat A D I C hD n x y)
  exact complexKFlat_of_iso A
    ((colimit.isColimit _).coconePointUniqueUpToIso (C.lengthIsColimit A D I x y)).symm h

end Attachment

variable [Small.{u} D]

/--
概要：閉元被覆からの生成元添加列の全段階の Hom は K-flat。
方針：初期の自由な球被覆と、語長フィルトレーションによる添加閉性を使う。
規約：元の dg 圏の Hom には K-flat 性を仮定しない。
使われ方：Drinfeld Lemma 13.5 の段階分解。
-/
theorem stage_kFlat (n : ℕ) : (DGCategoryCellResolution.stage A D n).HomKFlat := by
  induction n with
  | zero => exact DGCategoryCellResolution.initial_homKFlat A D
  | succ n ih =>
      let S := DGCategoryCellResolution.stage A D n
      exact @attachment_kFlat A _ D S.category S.CellIndex inferInstance S.cells ih

/--
概要：生成元添加列の余極限の Hom 複体は K-flat。
方針：各段階のフィルトレーションの証明と、加群圏の完全な逐次余極限を使う。
規約：次数ごとの自由性だけで非有界な結論を出さない。
使われ方：Drinfeld Lemma 13.5 から Thm 3.4 の平坦条件への接続。
-/
theorem limitHom_kFlat (x y : D) :
    complexKFlat A (DGCategoryCellResolution.candidateHom A D x y) := by
  have : AB5OfSize.{0, 0} (ModuleCat.{u} A) := AB5OfSize_of_univLE (ModuleCat.{u} A)
  exact complexKFlat_colimit A (DGCategoryCellResolution.homDiagram A D x y)
    (fun n => stage_kFlat A D n x y)

end SerrePositivity.KST.DerivedGeometry.DGResolution
