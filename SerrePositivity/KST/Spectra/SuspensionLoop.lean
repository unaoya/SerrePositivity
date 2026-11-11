module
public import SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.SuspensionLoop

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping
public import SerrePositivity.Spectra.PointedSimplicialSet.Monoidal

/-!
概要：点つき Kan 複体の suspension と loop の随伴。
方針：単体的円との smash と点つき内部 Hom の実構成を借りる。
規約：モデル構造を用いず、loop の Kan 性は相対ホーン充填で証明する。
使われ方：HA §1.4.2、BF 1978 §2、HTT A.3.3。Ω スペクトルの構造。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed SSet

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：Kan な点つき単体集合の loop 対象は Kan。
方針：点つき内部 Hom の相対充填を円に適用する。
規約：円自身の Kan 性は不要。
使われ方：HA §1.4.2、BF 1978 §2。Ω 条件のホモトピー群。 -/
instance loopSpace_kanComplex (X : PointedSimplicialSet.{u}) [KanComplex X.right] :
    KanComplex (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace X).right := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _

/-- 概要：suspension が点つき写像空間に誘導する単体的な射。
方針：smash の結合子と内部 Hom の評価を curry する。
規約：零次単体だけの関数ではなく、全単体次数で自然な射。
使われ方：BF 1978 §2、HTT A.3.3。切断スペクトルの境界比較。 -/
def suspensionHom (X Y : PointedSimplicialSet.{u}) :
    PointedObject.basedHom X Y ⟶ PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension Y) :=
  MonoidalClosed.curry
    ((α_ PointedSimplicialSet.circle.{u} X ((ihom X).obj Y)).hom ≫
      PointedSimplicialSet.circle.{u} ◁ ((ihom.ev X).app Y))

/-- 概要：suspension の写像空間への作用を評価した式。
方針：curry と uncurry の逆関係を使う。
規約：全て点つき対象の smash に関する等式。
使われ方：HTT A.3.3、BF 1978 §2。合成と構造写像との整合性。 -/
@[reassoc]
theorem suspensionHom_evaluation (X Y : PointedSimplicialSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X ◁ suspensionHom X Y ≫ (ihom.ev (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X)).app (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension Y) =
      (α_ PointedSimplicialSet.circle.{u} X ((ihom X).obj Y)).hom ≫
        PointedSimplicialSet.circle.{u} ◁ ((ihom.ev X).app Y) := by
  exact MonoidalClosed.uncurry_curry (A := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X)
    ((α_ PointedSimplicialSet.circle.{u} X ((ihom X).obj Y)).hom ≫
      PointedSimplicialSet.circle.{u} ◁ ((ihom.ev X).app Y))

/-- 概要：suspension の写像空間への作用は通常の射の suspension を延長する。
方針：評価との随伴と結合子・右単位子の自然性を使う。
規約：curry' は通常の射を内部 Hom の点として表す。
使われ方：BF 1978 §2、HTT A.3.3。写像空間の零次単体とスペクトルの射の照合。 -/
theorem suspensionHom_curry' {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y) :
    MonoidalClosed.curry' f ≫ suspensionHom X Y =
      MonoidalClosed.curry' (PointedSimplicialSet.circle.{u} ◁ f) := by
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left, suspensionHom, MonoidalClosed.uncurry_curry]
  conv_rhs => rw [MonoidalClosed.curry', MonoidalClosed.uncurry_curry]
  change _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X ◁ MonoidalClosed.curry' f ≫
      ((α_ PointedSimplicialSet.circle.{u} X ((ihom X).obj Y)).hom ≫
        PointedSimplicialSet.circle.{u} ◁ ((ihom.ev X).app Y)) =
    (ρ_ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X)).hom ≫ PointedSimplicialSet.circle.{u} ◁ f
  rw [associator_naturality_right_assoc]
  rw [← whiskerLeft_comp, MonoidalClosed.whiskerLeft_curry'_ihom_ev_app]
  rw [whiskerLeft_comp, ← Category.assoc, ← rightUnitor_tensor_hom]

end

end SerrePositivity.KST.Spectra
