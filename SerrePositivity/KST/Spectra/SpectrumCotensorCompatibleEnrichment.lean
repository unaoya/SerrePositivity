module

public import SerrePositivity.KST.Spectra.SpectrumCotensorCompatibleLaws
public import SerrePositivity.CategoryTheory.Enriched.Transport

/-!
概要：cotensor の評価と可換な射の組からなる局所 Kan な単体的圏。
方針：点つき豊穣構造を忘却関手で移送し、その単位からの射を通常の射とする。
規約：パラメータ A ごとに元の対象を包む。使われ方：coherent な cotensor 関手化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.CotensorCompatible

/-- 整合写像空間を Hom とする圏の対象。 -/
structure Object (A : PointedSimplicialSet.{u}) where
  /-- 元の BF 対象。 -/
  val : OmegaSpectrum.{u}

/-- 普遍評価と可換な射の組の点つき豊穣構造。 -/
instance pointedEnrichedCategory (A : PointedSimplicialSet.{u}) :
    EnrichedCategory PointedSimplicialSet.{u} (Object A) where
  Hom X Y := pointedSpace A X.val Y.val
  id X := identity A X.val
  comp X Y Z := composition A X.val Y.val Z.val
  id_comp X Y := identity_composition A X.val Y.val
  comp_id X Y := composition_identity A X.val Y.val
  assoc W X Y Z := composition_assoc A W.val X.val Y.val Z.val

/-- 同じ対象と、元の組の基礎単体集合からなる豊穣構造。 -/
instance simplicialEnrichedCategory (A : PointedSimplicialSet.{u}) :
    EnrichedCategory SSet.{u} (Object A) :=
  TransportEnrichmentComparisons.category PointedSimplicialSet.forget.{u} (Object A)

/-- 単位からの豊穣射を通常の射とする圏構造。 -/
instance category (A : PointedSimplicialSet.{u}) : Category.{u} (Object A) :=
  inferInstanceAs (Category (ForgetEnrichment SSet.{u} (Object A)))

/-- 通常の射と豊穣単位からの射の対応を備えた単体的圏。 -/
instance simplicialCategory (A : PointedSimplicialSet.{u}) : SimplicialCategory (Object A) where
  homEquiv := Equiv.refl _
  homEquiv_id X := ForgetEnrichment.homTo_id (W := SSet.{u}) (C := Object A) X
  homEquiv_comp f g := ForgetEnrichment.homTo_comp (W := SSet.{u}) (C := Object A) f g

/-- 整合写像空間は元の Kan な引き戻しそのもの。 -/
instance hom_kanComplex (A : PointedSimplicialSet.{u}) (X Y : Object A) :
    KanComplex (SimplicialCategory.sHom X Y) := pointedSpace_kanComplex A X.val Y.val

end SerrePositivity.KST.Spectra.OmegaSpectrum.CotensorCompatible
