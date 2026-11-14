module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.RightFibrationYoneda
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorUnitHom
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Vertices
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Quasicategory

/-!
概要：固定した底上の小さい right fibrations の単体的圏とその coherent nerve。
方針：底上の射を通常の射とし、相対関手空間を Kan な豊穣 Hom として γ1 を適用する。
規約：全空間と底は u、coherent nerve は u+1。極限・余極限は主張しない。
使われ方：Kerodon §8.1（Tag 03JB）、前層分類の fibration 側の関手 ∞ 圏の比較先。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

/-- 概要：固定した底上の小さい right fibration を束縛した対象。
方針：Over 圏の対象と、その射影の right fibration 性を部分型にまとめる。
規約：全空間は宇宙 u の単体集合。
使われ方：Kerodon §8.1（Tag 03JB）、分類の fibration 側の対象。 -/
def RightFibrationObject (B : SSet.{u}) := {p : Over B // _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration p.hom}

/-- 概要：right fibration の対象は底上の射を通常の射とする圏をなす。
方針：Over 圏の恒等・合成とその法則を継承する。
規約：同値類で商にせず、厳密な底上の射を使う。
使われ方：Kerodon §8.1（Tag 03JB）、単体的圏の通常の圏構造。 -/
instance rightFibrationObject_category (B : SSet.{u}) : Category.{u} (RightFibrationObject B) where
  Hom p q := p.val ⟶ q.val
  id p := 𝟙 p.val
  comp f g := f ≫ g
  id_comp f := Category.id_comp f
  comp_id f := Category.comp_id f
  assoc f g h := Category.assoc f g h

/-- 概要：束縛した対象の射影は right fibration。
方針：部分型に記録した証明を取り出す。
規約：底の quasicategory 性は不要。
使われ方：Kerodon §8.1（Tag 03JB）、豊穣 Hom の Kan 性。 -/
instance rightFibrationObject_projection {B : SSet.{u}} (p : RightFibrationObject B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration p.val.hom := p.property

/-- 概要：固定底上の right fibrations は相対関手空間で豊穣化される。
方針：相対豊穣単位・合成とその三法則を使う。
規約：Hom は fiber ごとの射の集合ではなく相対関手単体集合。
使われ方：Kerodon §8.1（Tag 03JB）、分類の fibration 側の単体的圏。 -/
instance rightFibrationObject_enrichedCategory (B : SSet.{u}) :
    EnrichedCategory SSet.{u} (RightFibrationObject B) where
  Hom p q := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q.val.hom p.val.hom
  id p := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorIdentity p.val
  comp p q r := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorComposition p.val q.val r.val
  id_comp p q := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorIdentity_comp p.val q.val
  comp_id p q := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorComposition_id p.val q.val
  assoc p q r s := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorComposition_assoc p.val q.val r.val s.val

/-- 概要：通常の底上の射と豊穣 Hom の零単体は整合し、単体的圏をなす。
方針：相対関手の単位からの射の全単射と、恒等・合成の整合性を使う。
規約：通常の射の同一視には選択したホモトピー逆を使わない。
使われ方：Kerodon §8.1（Tag 03JB）、coherent nerve の入力。 -/
noncomputable instance rightFibrationObject_simplicialCategory (B : SSet.{u}) :
    SimplicialCategory (RightFibrationObject B) where
  homEquiv {p q} := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorHomEquiv p.val q.val
  homEquiv_id p := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorHomEquiv_id p.val
  homEquiv_comp {p q r} f g :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorHomEquiv_comp (a := p.val) (b := q.val) (c := r.val) f g

/-- 概要：right fibrations の単体的圏の全ての豊穣 Hom は Kan 複体。
方針：標的の射影の right fibration 性から相対関手空間の Kan 性を使う。
規約：底自体の充填性は要求しない。
使われ方：Kerodon §8.1（Tag 03JB）、coherent nerve の γ1 の入力。 -/
instance rightFibrationObject_sHom_kanComplex {B : SSet.{u}} (p q : RightFibrationObject B) :
    KanComplex (SimplicialCategory.sHom p q) :=
  inferInstanceAs (KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q.val.hom p.val.hom))

/-- 概要：固定した底上の小さい right fibrations の ∞ 圏。
方針：相対関手空間を Hom とする単体的圏の coherent nerve を取る。
規約：全空間の小ささの宇宙は u、得られる単体集合は u+1。
使われ方：Kerodon §8.1（Tag 03JB）、前層分類の fibration 側。 -/
noncomputable def RightFibrationInfinity (B : SSet.{u}) : SSet.{u + 1} :=
  SimplicialNerve (RightFibrationObject B)

/-- 概要：right fibrations の coherent nerve は quasicategory。
方針：相対関手空間の局所 Kan 性に既存の γ1 を適用する。
規約：追加の充填仮定や分類定理は使わない。
使われ方：Kerodon §8.1（Tag 03JB）、分類の ∞ 圏としての比較先。 -/
instance rightFibrationInfinity_quasicategory (B : SSet.{u}) :
    Quasicategory (RightFibrationInfinity B) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialNerve_quasicategory (RightFibrationObject B)

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "2.2.3.8"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.RightFibrationObject
attribute [cite HTT "2.2.3.8"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.rightFibrationObject_category
attribute [cite HTT "2.2.3.8"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.rightFibrationObject_simplicialCategory
