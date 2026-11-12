module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.EnrichedHomCongrUnit

/-!
概要：同型で結ばれた対象の組を、始域の元の全 Hom で豊穣化する。
方針：通常の圏と豊穣構造を同じ始域の対象から厳密に移す。
規約：元の全高次 Hom を残し、零単体や大域 Hom の像に限定しない。
使われ方：同じ結合同型の両側の評価を全局所 Hom に自然な比較にする。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
open CategoryTheory
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories

/-- 同じ元の二対象と、その間の指定された同型。 -/
structure IsoTransportObject (C : Type w) [Category.{z} C] where
  source : C
  target : C
  comparison : source ≅ target

/-- 元の始域の全ての通常の射を Hom とする。 -/
instance isoTransportObject_category {C : Type w} [Category.{z} C] :
    Category.{z} (IsoTransportObject C) where
  Hom X Y := X.source ⟶ Y.source
  id X := 𝟙 X.source
  comp f g := f ≫ g
  id_comp f := Category.id_comp f
  comp_id f := Category.comp_id f
  assoc f g h := Category.assoc f g h

/-- 元の始域の全ての豊穣 Hom と同じ通常の射の豊穣表示を保持する。 -/
instance isoTransportObject_enrichedOrdinaryCategory
    (V : Type u) [Category.{v} V] [MonoidalCategory V]
    {C : Type w} [Category.{z} C] [EnrichedOrdinaryCategory V C] :
    EnrichedOrdinaryCategory V (IsoTransportObject C) where
  Hom X Y := X.source ⟶[V] Y.source
  id X := eId V X.source
  comp X Y Z := eComp V X.source Y.source Z.source
  id_comp X Y := e_id_comp V X.source Y.source
  comp_id X Y := e_comp_id V X.source Y.source
  assoc W X Y Z := e_assoc V W.source X.source Y.source Z.source
  homEquiv {X Y} := eHomEquiv V (X := X.source) (Y := Y.source)
  homEquiv_id X := eHomEquiv_id V X.source
  homEquiv_comp {X Y Z} f g :=
    eHomEquiv_comp V (X := X.source) (Y := Y.source) (Z := Z.source) f g

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
