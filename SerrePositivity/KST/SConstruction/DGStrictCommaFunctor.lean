module
public import SerrePositivity.KST.SConstruction.DGStrictCommaComposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaProjections

/-! # 全 Hom 上の閉比較から作る厳密 dg comma 関手
概要：元の二関手と全 Hom 自然な閉比較を、実 comma 値 dg 関手へ束ねる。
方針：同じ Hom 作用の単位・合成保存を使い、両実射影との厳密な等号を回収する。
規約：離散 Hom に置換しない。使われ方：元の二成分による標準対角の構成。
-/
@[expose] public section
noncomputable section
universe u v w t
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable {R : Type u} [CommRing R] {C : Type v} [DGCategory R C]
  {E : Type w} [DGCategory R E] {F : DGFunctor R C E}
  {P : Type t} [DGCategory R P]
namespace DGStrictCommaFamily
variable (d : DGStrictCommaFamily R C E F P)

/-- 元の二関手と同じ閉比較を持ち、全 Hom 作用を保つ実 dg 関手。 -/
def toDGFunctor : DGFunctor R P (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F) where
  obj := d.obj
  map := d.homMap
  map_id := d.homMap_id
  map_comp := d.homMap_comp

/-- 同じ実 dg 関手の入力射影は、元の第一関手そのもの。 -/
lemma toDGFunctor_source :
    d.toDGFunctor.comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSource R C E F) = d.source := by
  apply EnrichedFunctor.ext (Complex R)
    (F := d.toDGFunctor.comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSource R C E F)) (G := d.source)
    (fun _ => rfl)
  intro x y
  change (d.homMap x y ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSourceHomMap R C E F (d.obj x) (d.obj y)) ≫
    𝟙 _ = d.source.map x y
  exact (Category.comp_id _).trans (d.homMap_source x y)

/-- 同じ実 dg 関手の比較対象射影は、元の第二関手そのもの。 -/
lemma toDGFunctor_replacement :
    d.toDGFunctor.comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacement R C E F) = d.replacement := by
  apply EnrichedFunctor.ext (Complex R)
    (F := d.toDGFunctor.comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacement R C E F)) (G := d.replacement)
    (fun _ => rfl)
  intro x y
  change (d.homMap x y ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R C E F (d.obj x) (d.obj y)) ≫
      𝟙 _ = d.replacement.map x y
  exact (Category.comp_id _).trans (d.homMap_replacement x y)

/-- 同じ実対象の閉比較は、元の指定 augmentation を厳密に回収する。 -/
lemma toDGFunctor_augmentation (x : P) :
    (d.toDGFunctor.obj x).augmentation = d.augmentation x := rfl

end DGStrictCommaFamily
end SerrePositivity.KST.SConstruction
