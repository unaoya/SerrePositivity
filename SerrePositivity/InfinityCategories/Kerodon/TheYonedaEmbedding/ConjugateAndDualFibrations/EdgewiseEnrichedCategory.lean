module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEdgewiseFunctor
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.HomComparison
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：各豊穣 Hom を edgewise 解像で置き換えた単体的圏。
方針：重みからの射を点ごとに合成し、元の豊穣単位・合成の三法則を評価する。
規約：対象は元の単体的圏の対象を自明な部分型に包み、通常の射は新しい豊穣単位からの射。
使われ方：Kerodon §8.1.1（Tag 03JF）、Corollary 5.6.0.6（Tag 028T）、左右の Hom の coherent な共通解像。

対応節は Kerodon 8.6（Tag 04C0）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.ConjugateAndDualFibrations

/-- 概要：Hom を edgewise 解像で置き換える圏の対象。
方針：元の対象を自明な部分型に包み、新しい通常の圏構造を与えられるようにする。
規約：対象の選択や商は追加しない。
使われ方：Kerodon §8.1.1（Tag 03JF）、豊穣 Hom の共通解像の対象。 -/
@[kerodon 04F9]
def EdgewiseEnrichedObject (C : Type v) := {_c : C // True}

/-- 概要：edgewise な豊穣 Hom の恒等射。
方針：全ての重みからテンソル単位を通る元の豊穣恒等射を取る。
規約：重みのパラメーターに定値。
使われ方：Kerodon §2.4.3（Tag 00KM）、§8.1.1（Tag 03JF）、解像した豊穣圏の単位。 -/
def edgewiseEnrichedIdentity {C : Type v} [Category.{u} C] [SimplicialCategory C] (X : C) :
    𝟙_ SSet.{u} ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision (SimplicialCategory.sHom X X) where
  app d := ↾fun _ ↦ toUnit (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.obj d.unop) ≫ eId SSet X
  naturality {d e} α := by
    apply ConcreteCategory.hom_ext
    intro a
    change toUnit (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.obj e.unop) ≫ eId SSet X =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map α.unop ≫ (toUnit (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.obj d.unop) ≫ eId SSet X)
    rw [← Category.assoc, comp_toUnit]

/-- 概要：edgewise な豊穣 Hom の合成。
方針：二つの重みからの射を対にして元の豊穣合成へ送る。
規約：同じ重みのパラメーターで両方の射を評価する。
使われ方：Kerodon §2.4.3（Tag 00KM）、§8.1.1（Tag 03JF）、解像した高次の Hom の合成。 -/
@[kerodon 04F9]
def edgewiseEnrichedComposition {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (X Y Z : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision (SimplicialCategory.sHom X Y) ⊗
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision (SimplicialCategory.sHom Y Z) ⟶
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision (SimplicialCategory.sHom X Z) where
  app _ := ↾fun ⟨f, g⟩ ↦ lift f g ≫ eComp SSet X Y Z
  naturality {d e} α := by
    apply ConcreteCategory.hom_ext
    rintro ⟨f, g⟩
    change lift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map α.unop ≫ f) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map α.unop ≫ g) ≫
      eComp SSet X Y Z = _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map α.unop ≫ (lift f g ≫ eComp SSet X Y Z)
    rw [← Category.assoc, comp_lift]

/-- 概要：edgewise な豊穣単位は左の合成から消去される。
方針：重みの全単体で元の豊穣圏の左単位則を評価する。
規約：元の Hom に Kan 性を要求しない。
使われ方：Kerodon §2.4.3（Tag 00KM）、edgewise な豊穣圏の左単位則。 -/
lemma edgewiseEnrichedIdentity_comp {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (X Y : C) :
    (λ_ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision (SimplicialCategory.sHom X Y))).inv ≫
      edgewiseEnrichedIdentity X ▷ _ ≫ edgewiseEnrichedComposition X X Y = 𝟙 _ := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro f
  apply SSet.hom_ext
  intro e
  apply ConcreteCategory.hom_ext
  intro x
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_id_comp_app X Y e (f.app e x)

/-- 概要：edgewise な豊穣単位は右の合成から消去される。
方針：重みの全単体で元の豊穣圏の右単位則を評価する。
規約：元の Hom に Kan 性を要求しない。
使われ方：Kerodon §2.4.3（Tag 00KM）、edgewise な豊穣圏の右単位則。 -/
lemma edgewiseEnrichedComposition_id {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (X Y : C) :
    (ρ_ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision (SimplicialCategory.sHom X Y))).inv ≫
      _ ◁ edgewiseEnrichedIdentity Y ≫ edgewiseEnrichedComposition X Y Y = 𝟙 _ := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro f
  apply SSet.hom_ext
  intro e
  apply ConcreteCategory.hom_ext
  intro x
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_comp_id_app X Y e (f.app e x)

/-- 概要：edgewise な豊穣合成は結合的。
方針：重みの各単体で元の豊穣結合則を評価する。
規約：三つの射は同じパラメーターで評価される。
使われ方：Kerodon §2.4.3（Tag 00KM）、edgewise な豊穣圏の結合則。 -/
lemma edgewiseEnrichedComposition_assoc {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (W X Y Z : C) :
    (α_ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision (SimplicialCategory.sHom W X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision (SimplicialCategory.sHom X Y))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision (SimplicialCategory.sHom Y Z))).inv ≫
      edgewiseEnrichedComposition W X Y ▷ _ ≫ edgewiseEnrichedComposition W Y Z =
    _ ◁ edgewiseEnrichedComposition X Y Z ≫ edgewiseEnrichedComposition W X Z := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  rintro ⟨f, g, h⟩
  apply SSet.hom_ext
  intro e
  apply ConcreteCategory.hom_ext
  intro x
  exact congrArg (fun m :
      SimplicialCategory.sHom W X ⊗ (SimplicialCategory.sHom X Y ⊗ SimplicialCategory.sHom Y Z) ⟶
        SimplicialCategory.sHom W Z ↦ m.app e (f.app e x, g.app e x, h.app e x))
    (e_assoc SSet W X Y Z)

/-- 概要：元の単体的圏の Hom の edgewise 解像は豊穣圏をなす。
方針：重みからの射の単位・合成とその三法則を束縛する。
規約：この構造自体には局所 Kan 性を要求しない。
使われ方：Kerodon §8.1.1（Tag 03JF）、Corollary 5.6.0.6（Tag 028T）、左右の豊穣 Hom 比較の共通始域。 -/
instance edgewiseEnrichedObject_enrichedCategory (C : Type v)
    [Category.{u} C] [SimplicialCategory C] :
    EnrichedCategory SSet.{u} (EdgewiseEnrichedObject C) where
  Hom X Y := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision (SimplicialCategory.sHom X.val Y.val)
  id X := edgewiseEnrichedIdentity X.val
  comp X Y Z := edgewiseEnrichedComposition X.val Y.val Z.val
  id_comp X Y := edgewiseEnrichedIdentity_comp X.val Y.val
  comp_id X Y := edgewiseEnrichedComposition_id X.val Y.val
  assoc W X Y Z := edgewiseEnrichedComposition_assoc W.val X.val Y.val Z.val

/-- 概要：edgewise な豊穣圏の通常の射は豊穣単位からの射。
方針：豊穣圏の underlying category を使う。
規約：元の圏の通常の Hom とは別の圏構造。
使われ方：Kerodon §2.4.3（Tag 00KM）、edgewise な豊穣圏の coherent nerve の入力。 -/
instance edgewiseEnrichedObject_category (C : Type v) [Category.{u} C] [SimplicialCategory C] :
    Category.{u} (EdgewiseEnrichedObject C) :=
  inferInstanceAs (Category (ForgetEnrichment SSet.{u} (EdgewiseEnrichedObject C)))

/-- 概要：edgewise な豊穣構造と underlying category は単体的圏をなす。
方針：豊穣単位からの射の恒等の全単射と既存の単位・合成則を使う。
規約：coherent nerve に局所 Kan 性を別に与えられる。
使われ方：Kerodon §2.4.3（Tag 00KM）、§8.1.1（Tag 03JF）、edgewise な coherent nerve の構成。 -/
@[kerodon 04F9]
instance edgewiseEnrichedObject_simplicialCategory (C : Type v)
    [Category.{u} C] [SimplicialCategory C] : SimplicialCategory (EdgewiseEnrichedObject C) where
  homEquiv := Equiv.refl _
  homEquiv_id X := ForgetEnrichment.homTo_id (W := SSet.{u}) (C := EdgewiseEnrichedObject C) X
  homEquiv_comp f g := by
    exact ForgetEnrichment.homTo_comp (W := SSet.{u}) (C := EdgewiseEnrichedObject C) f g

/-- 概要：局所 Kan な単体的圏の edgewise な豊穣圏も局所 Kan。
方針：各 Hom に edgewise subdivision の Kan 性を適用する。
規約：元の全ての豊穣 Hom の Kan 性を仮定する。
使われ方：Kerodon §8.1.1（Tag 03JF）、Corollary 5.6.0.6（Tag 028T）、coherent nerve の比較を同値として扱う。 -/
@[kerodon 04FA, kerodon 04FD]
instance edgewiseEnrichedObject_sHom_kanComplex {C : Type v} [Category.{u} C] [SimplicialCategory C]
    [∀ X Y : C, KanComplex (SimplicialCategory.sHom X Y)] (X Y : EdgewiseEnrichedObject C) :
    KanComplex (SimplicialCategory.sHom X Y) :=
  inferInstanceAs (KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision (SimplicialCategory.sHom X.val Y.val)))

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.ConjugateAndDualFibrations
