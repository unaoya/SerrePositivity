module

public import SerrePositivity.KST.Spectra.AdjointLoopRelativeFullCompatibleLaws
public import SerrePositivity.CategoryTheory.Enriched.BaseChange

/-!
概要：相対 BF 左右因子と厳密可換な全 Hom の組の局所 Kan な単体的圏。
方針：実引き戻しの全単体上の合成・単位を使う。
規約：選択した持ち上げの通常関手性を仮定しない。
使われ方：元の対象と置換後の対象への全図式の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF

/-- 概要：相対 BF 比較を保つ豊穣圏の対象。
方針：元の BF 対象を包む。
規約：対象の選択を増やさない。
使われ方：元の全 Hom と置換の全 Hom の同時回収。 -/
structure FullObject where
  /-- 概要：元の BF 対象。
方針：元の全 Hom と実引き戻しの法則を使う。
規約：全パラメータを保持する。
使われ方：相対 BF 比較の豊穣構造。 -/
  val : OmegaSpectrum.{u}

/-- 概要：元の左右因子を同時に保つ全 Hom の単体的豊穣構造。
方針：実引き戻しと二射影で検証した厳密法則を使う。
規約：右射影の境界条件を保持する。
使われ方：元の指定単位と射影を保つ全図式比較。 -/
instance fullSimplicialEnrichedCategory :
    EnrichedCategory SSet.{u} FullObject where
  Hom X Y := fullCompatibleSpace X.val Y.val
  id X := fullCompatibleIdentity X.val
  comp X Y Z := fullCompatibleComposition X.val Y.val Z.val
  id_comp X Y := fullCompatibleIdentity_composition X.val Y.val
  comp_id X Y := fullCompatibleComposition_identity X.val Y.val
  assoc W X Y Z := fullCompatibleComposition_assoc W.val X.val Y.val Z.val

/-- 概要：単位からの豊穣射を通常の射とする圏構造。
方針：元の全 Hom と実引き戻しの法則を使う。
規約：全パラメータを保持する。
使われ方：相対 BF 比較の豊穣構造。 -/
instance fullCategory : Category.{u} FullObject :=
  inferInstanceAs (Category (ForgetEnrichment SSet.{u} FullObject))

/-- 概要：通常の射と豊穣単位からの射の対応を備えた単体的圏。
方針：元の全 Hom と実引き戻しの法則を使う。
規約：全パラメータを保持する。
使われ方：相対 BF 比較の豊穣構造。 -/
instance fullSimplicialCategory : SimplicialCategory FullObject where
  homEquiv := Equiv.refl _
  homEquiv_id X := ForgetEnrichment.homTo_id (W := SSet.{u}) (C := FullObject) X
  homEquiv_comp f g := ForgetEnrichment.homTo_comp (W := SSet.{u}) (C := FullObject) f g

/-- 概要：整合写像空間は元の Kan な引き戻しそのもの。
方針：元の全 Hom と実引き戻しの法則を使う。
規約：全パラメータを保持する。
使われ方：相対 BF 比較の豊穣構造。 -/
instance fullHom_kanComplex (X Y : FullObject) :
    KanComplex (SimplicialCategory.sHom X Y) := fullCompatibleSpace_kanComplex X.val Y.val

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
