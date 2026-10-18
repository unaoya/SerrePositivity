module
public import SerrePositivity.KST.ProExcision.RelativeBar

/-!
# 基底を変える半直積対の相対 bar 写像

概要：基底を変える実単体射の可換正方形を相対 bar 項へ降ろす。
方針：基底射・全空間射・標準包含の可換性を実データとし、商の合成則を適用する。
規約：KST Claim 4.15 の rank 変更。H_* 自体の定義は所有レーンから借りる。
使われ方：Lemma A.4 の零写像を大きい rank の相対項へ後合成する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory
open SerrePositivity.KST.Comparison
variable {G H G' H' G'' H'' : SimplicialObject MonCat.{u}}

/-- 概要：基底変更を許す半直積対の実射。
方針：二つの単体射と標準包含の可換性だけを保持する。
規約：KST Claim 4.15、相対零化やホモロジーの結論は含まない。
使われ方：異なる有限 rank の相対項を結ぶ。 -/
structure SimplicialActionPairMap (A : SimplicialMonoidAction G H)
    (B : SimplicialMonoidAction G' H') where
  base : G ⟶ G'
  total : simplicialActionProduct A ⟶ simplicialActionProduct B
  section_comm : simplicialActionProductSection A ≫ total = base ≫ simplicialActionProductSection B

/-- 概要：半直積対の実射の合成。
方針：基底射と全空間射をそれぞれ合成する。
規約：KST Claim 4.15。使われ方：実相対写像の因子化。 -/
def SimplicialActionPairMap.comp {A : SimplicialMonoidAction G H}
    {B : SimplicialMonoidAction G' H'} {C : SimplicialMonoidAction G'' H''}
    (f : SimplicialActionPairMap A B) (g : SimplicialActionPairMap B C) :
    SimplicialActionPairMap A C where
  base := f.base ≫ g.base
  total := f.total ≫ g.total
  section_comm := by
    rw [← Category.assoc, f.section_comm, Category.assoc, g.section_comm, ← Category.assoc]

/-- 概要：同じ基底での同変射を半直積対の射として読む。
方針：基底を恒等射、全空間を構成済みの半直積誘導射にする。
規約：KST Lemma A.4。使われ方：低次の零写像を基底変更の射へ接続する。 -/
def SimplicialActionHom.toPairMap {A : SimplicialMonoidAction G H}
    {B : SimplicialMonoidAction G H'} (f : SimplicialActionHom A B) :
    SimplicialActionPairMap A B where
  base := 𝟙 G
  total := simplicialActionProductMap f
  section_comm := by rw [simplicialActionProductSection_map, Category.id_comp]

/-- 概要：基底変更を許す実対射が相対 bar 項に誘導する写像。
方針：可換正方形を bar と借用関手で写し、実余核へ降ろす。
規約：KST Claim 4.15。使われ方：有限 rank の相対ホモロジーの写像。 -/
def relativeBarPairMap (F : SSet.{u} ⥤ ModuleCat.{u} ℤ)
    {A : SimplicialMonoidAction G H} {B : SimplicialMonoidAction G' H'}
    (f : SimplicialActionPairMap A B) : relativeBarModule F A ⟶ relativeBarModule F B :=
  relativeModuleMap _ _ (F.map (monoidBarMap f.base)) (F.map (monoidBarMap f.total)) (by
    rw [← F.map_comp, ← F.map_comp, ← monoidBarMap_comp, ← monoidBarMap_comp, f.section_comm])

/-- 概要：半直積対の相対 bar 写像は合成を保つ。
方針：余核の実商の合成則と二つの関手の合成則を使う。
規約：KST Claim 4.15。使われ方：A.4 の零写像の後合成。 -/
lemma relativeBarPairMap_comp (F : SSet.{u} ⥤ ModuleCat.{u} ℤ)
    {A : SimplicialMonoidAction G H} {B : SimplicialMonoidAction G' H'}
    {C : SimplicialMonoidAction G'' H''}
    (f : SimplicialActionPairMap A B) (g : SimplicialActionPairMap B C) :
    relativeBarPairMap F (f.comp g) = relativeBarPairMap F f ≫ relativeBarPairMap F g := by
  unfold relativeBarPairMap
  rw [relativeModuleMap_comp]
  apply relativeModuleMap_eq_of_right_eq
  rw [← F.map_comp, ← monoidBarMap_comp]
  rfl

/-- 概要：同変射の対射としての相対写像は既存の相対写像と一致する。
方針：恒等基底の bar と関手の単位保存を使う。
規約：KST Lemma A.4。使われ方：既証明の低次零化の移送。 -/
lemma relativeBarPairMap_toPairMap (F : SSet.{u} ⥤ ModuleCat.{u} ℤ)
    {A : SimplicialMonoidAction G H} {B : SimplicialMonoidAction G H'}
    (f : SimplicialActionHom A B) : relativeBarPairMap F f.toPairMap = relativeBarMap F f := by
  apply relativeModuleMap_eq_of_right_eq
  rfl

end SerrePositivity.KST.ProExcision
