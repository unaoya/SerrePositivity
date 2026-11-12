module

public import SerrePositivity.KST.Spectra.FreePointedHom
public import SerrePositivity.KST.Spectra.PointedMappingNaturality

/-!
概要：自由基点からの内部 Hom の同型を源の制限として明示する。
方針：元の成分へ制限し、逆写像は新しい基点成分で基点に定数となるよう延長する。
規約：同型の順射を具体的に固定し、両変数の自然性を検証できる形にする。
使われ方：HA §1.4.2、BF 1978 §2。点つき end の成分の自然な比較。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet

namespace SerrePositivity.KST.Spectra.FreePointedHomRestriction

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：余積を源とする内部 Hom への射は二成分での制限で決まる。
方針：uncurry の単射性と余積の tensor の普遍性を使う。
規約：全て通常の単体集合の射。
使われ方：HA §1.4.2。自由基点の延長と制限の逆関係。 -/
theorem coprod_pre_hom_ext {A B Y P : SSet.{u}}
    {f g : P ⟶ (ihom (A ⨿ B)).obj Y}
    (h₁ : f ≫ (pre (coprod.inl : A ⟶ A ⨿ B)).app Y =
      g ≫ (pre (coprod.inl : A ⟶ A ⨿ B)).app Y)
    (h₂ : f ≫ (pre (coprod.inr : B ⟶ A ⨿ B)).app Y =
      g ≫ (pre (coprod.inr : B ⟶ A ⨿ B)).app Y) : f = g := by
  apply uncurry_injective
  apply PointedObject.tensorRightCoprod_hom_ext
  · simpa only [uncurry_pre_app] using congrArg uncurry h₁
  · simpa only [uncurry_pre_app] using congrArg uncurry h₂

/-- 概要：自由に加えた基点を除いた元の成分への制限。
方針：点つき Hom の包含に余積の第一成分による pre を合成する。
規約：定義上の具体的な順射。
使われ方：HA §1.4.2。点つき end を Kan end へ比較する成分。 -/
def restrict (A : SSet.{u}) (Y : PointedSimplicialSet.{u}) :
    (PointedObject.basedHom (PointedObject.adjoin A) Y).right ⟶ (ihom A).obj Y.right :=
  PointedObject.basedHomι (PointedObject.adjoin A) Y ≫
    (pre (coprod.inl : A ⟶ A ⨿ 𝟙_ SSet.{u})).app Y.right

/-- 概要：元の成分の射を新しい基点で定数となる射に延長する。
方針：tensor した余積から評価射と定数射を貼り合わせて curry する。
規約：点つき条件を課す前の通常の内部 Hom への射。
使われ方：HA §1.4.2。自由基点からの Hom の逆比較の構成。 -/
def extendRaw (A : SSet.{u}) (Y : PointedSimplicialSet.{u}) :
    (ihom A).obj Y.right ⟶ (ihom (PointedObject.adjoin A).right).obj Y.right :=
  curry (PointedObject.tensorRightDesc ((ihom.ev A).app Y.right)
    (toUnit (𝟙_ SSet.{u} ⊗ (ihom A).obj Y.right) ≫ Y.hom))

/-- 概要：延長は新しい基点成分で基点に定数。
方針：余積の第二成分で tensor の貼り合わせを評価する。
規約：通常の内部 Hom の射の等式。
使われ方：HA §1.4.2。等化子への持ち上げの入力。 -/
theorem extendRaw_base (A : SSet.{u}) (Y : PointedSimplicialSet.{u}) :
    extendRaw A Y ≫ PointedObject.homRestriction (PointedObject.adjoin A) Y =
      extendRaw A Y ≫ PointedObject.homConstant (PointedObject.adjoin A) Y := by
  change extendRaw A Y ≫ (pre (coprod.inr : 𝟙_ SSet.{u} ⟶ A ⨿ 𝟙_ SSet.{u})).app Y.right =
    extendRaw A Y ≫ (toUnit _ ≫ PointedObject.homBasepoint PointedObject.point Y)
  rw [extendRaw, curry_pre_app, PointedObject.tensorRightDesc_inr, comp_toUnit_assoc]
  exact PointedObject.curry_constant Y.hom

/-- 概要：新しい基点で定数となる延長を点つき内部 Hom へ持ち上げる。
方針：基点の等化子条件を使う。
規約：通常の単体集合の射としての逆比較。
使われ方：HA §1.4.2、BF 1978 §2。点つき weighted end の比較。 -/
def extend (A : SSet.{u}) (Y : PointedSimplicialSet.{u}) :
    (ihom A).obj Y.right ⟶ (PointedObject.basedHom (PointedObject.adjoin A) Y).right :=
  equalizer.lift (extendRaw A Y) (extendRaw_base A Y)

/-- 概要：延長を点つき Hom の包含へ合成すると元の延長。
方針：等化子の持ち上げの式を使う。
規約：厳密な等式。
使われ方：HA §1.4.2。延長と制限の計算。 -/
@[reassoc (attr := simp)]
theorem extend_ι (A : SSet.{u}) (Y : PointedSimplicialSet.{u}) :
    extend A Y ≫ PointedObject.basedHomι (PointedObject.adjoin A) Y = extendRaw A Y :=
  equalizer.lift_ι _ _

/-- 概要：延長して元の成分へ制限すると恒等。
方針：余積の第一成分の評価は元の内部 Hom の評価射である。
規約：通常の単体集合の等式。
使われ方：HA §1.4.2。具体的な比較同型の片方の逆関係。 -/
theorem extend_restrict (A : SSet.{u}) (Y : PointedSimplicialSet.{u}) :
    extend A Y ≫ restrict A Y = 𝟙 _ := by
  rw [restrict, ← Category.assoc, extend_ι, extendRaw, curry_pre_app,
    PointedObject.tensorRightDesc_inl, ← uncurry_id_eq_ev, curry_uncurry]

/-- 概要：元の成分への制限と基点成分での定数延長は点つき Hom の恒等。
方針：包含後で二つの余積成分へ制限し、それぞれの値を比較する。
規約：基点での制限は等化子条件を使う。
使われ方：HA §1.4.2。具体的な比較同型のもう片方の逆関係。 -/
theorem restrict_extend (A : SSet.{u}) (Y : PointedSimplicialSet.{u}) :
    restrict A Y ≫ extend A Y = 𝟙 _ := by
  apply (cancel_mono (PointedObject.basedHomι (PointedObject.adjoin A) Y)).mp
  rw [Category.assoc, extend_ι, Category.id_comp]
  apply coprod_pre_hom_ext
  · rw [Category.assoc, extendRaw, curry_pre_app, PointedObject.tensorRightDesc_inl,
      ← uncurry_id_eq_ev, curry_uncurry, Category.comp_id]
    rfl
  · have hc := PointedObject.basedHomι_condition (PointedObject.adjoin A) Y
    change PointedObject.basedHomι (PointedObject.adjoin A) Y ≫
      (pre (coprod.inr : 𝟙_ SSet.{u} ⟶ A ⨿ 𝟙_ SSet.{u})).app Y.right = _ at hc
    rw [Category.assoc, extendRaw, curry_pre_app, PointedObject.tensorRightDesc_inr,
      PointedObject.curry_constant, hc]
    simp only [PointedObject.homConstant, comp_toUnit_assoc]
    rfl

/-- 概要：元の成分への制限は標的の点つき射に関して自然。
方針：点つき Hom の包含の自然性と通常の pre の後合成の自然性を使う。
規約：標的の Kan 性は不要。
使われ方：HA §1.4.2。end の標的変数の構造射の比較。 -/
@[reassoc]
theorem natural_post (A : SSet.{u}) {Y Z : PointedSimplicialSet.{u}} (f : Y ⟶ Z) :
    (PointedObject.basedHomMap (PointedObject.adjoin A) f).right ≫ restrict A Z =
      restrict A Y ≫ (ihom A).map f.right := by
  rw [restrict, restrict, ← Category.assoc, PointedObject.basedHomMap_ι,
    Category.assoc, ← pre_comm_ihom_map, ← Category.assoc]

/-- 概要：元の成分への制限は自由基点を加える前の源の射に関して自然。
方針：点つき pre を包含へ戻し、余積の第一成分と源の射の可換式を使う。
規約：二変数の自然な end の比較に使う厳密な等式。
使われ方：HA §1.4.2、BF 1978 §2。pointed end の重み変数の比較。 -/
@[reassoc]
theorem natural_pre {A B : SSet.{u}} (f : A ⟶ B) (Y : PointedSimplicialSet.{u}) :
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (PointedObject.adjoinFunctor.map f) Y).right ≫ restrict A Y =
      restrict B Y ≫ (pre f).app Y.right := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (PointedObject.adjoinFunctor.map f) Y ≫
    (PointedObject.basedHomι (PointedObject.adjoin A) Y ≫ (pre coprod.inl).app Y.right) = _
  rw [← Category.assoc]
  erw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre_ι]
  rw [Category.assoc]
  change PointedObject.basedHomι (PointedObject.adjoin B) Y ≫
      ((pre (PointedObject.adjoinFunctor.map f).right).app Y.right ≫
        (pre (coprod.inl : A ⟶ A ⨿ 𝟙_ SSet.{u})).app Y.right) =
    (PointedObject.basedHomι (PointedObject.adjoin B) Y ≫
      (pre (coprod.inl : B ⟶ B ⨿ 𝟙_ SSet.{u})).app Y.right) ≫ (pre f).app Y.right
  rw [← NatTrans.comp_app, ← pre_map, Category.assoc, ← NatTrans.comp_app, ← pre_map]
  congr 2
  apply congrArg pre
  change (coprod.inl : A ⟶ A ⨿ 𝟙_ SSet.{u}) ≫ coprod.map f (𝟙 _) =
    f ≫ (coprod.inl : B ⟶ B ⨿ 𝟙_ SSet.{u})
  exact coprod.inl_map _ _

/-- 概要：自由基点を加えた源からの内部 Hom の同型を元の成分への制限で与える。
方針：定数延長と二つの逆関係を使う。
規約：順射は restrict そのもの。
使われ方：HA §1.4.2、BF 1978 §2。両変数に自然な pointed end の成分比較。 -/
def iso (A : SSet.{u}) (Y : PointedSimplicialSet.{u}) :
    (PointedObject.basedHom (PointedObject.adjoin A) Y).right ≅ (ihom A).obj Y.right where
  hom := restrict A Y
  inv := extend A Y
  hom_inv_id := restrict_extend A Y
  inv_hom_id := extend_restrict A Y

end

end SerrePositivity.KST.Spectra.FreePointedHomRestriction
