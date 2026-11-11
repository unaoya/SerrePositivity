module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalOppositeFibration

/-!
概要：left cofinality と反転した right cofinality の同値。
方針：anodyne・trivial Kan 因子分解を反転し、二重反転の同型で戻す。
規約：一般の単体集合の射に成立する。
使われ方：Quillen A の左右の判定の接続。

対応節は Kerodon 7.2（Tag 02MZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality

/-- 概要：同型な単体集合の射は left cofinal。
方針：同型の left anodyne 性による十分性を使う。
規約：元の対象は任意。
使われ方：二重反転の消去。 -/
lemma isLeftCofinal_of_isIso {A B : SSet.{u}} (f : A ⟶ B) [IsIso f] : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal f :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isLeftCofinal_of_leftAnodyne f (MorphismProperty.of_isIso _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions f)

/-- 概要：同型な単体集合の射は right cofinal。
方針：同型の right anodyne 性による十分性を使う。
規約：元の対象は任意。
使われ方：二重反転の消去。 -/
lemma isRightCofinal_of_isIso {A B : SSet.{u}} (f : A ⟶ B) [IsIso f] : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal f :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_of_rightAnodyne f (MorphismProperty.of_isIso _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions f)

/-- 概要：矢の同型で left cofinality を移せる。
方針：両端の同型と元の cofinal な射を合成する。
規約：同型の向きは元の射 f から新しい射 g。
使われ方：反転を二度行った射を元の射へ戻す。 -/
lemma IsLeftCofinal.of_arrow_iso {A B A' B' : SSet.{u}} {f : A ⟶ B} {g : A' ⟶ B'}
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal f) (e : Arrow.mk f ≅ Arrow.mk g) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal g := by
  let a := (Arrow.leftFunc.mapIso e).inv
  let b := (Arrow.rightFunc.mapIso e).hom
  have h := (isLeftCofinal_of_isIso a).comp (hf.comp (isLeftCofinal_of_isIso b))
  have he : a ≫ (f ≫ b) = g := by
    have hw : e.hom.left ≫ g = f ≫ e.hom.right := e.hom.w
    change e.inv.left ≫ (f ≫ e.hom.right) = g
    rw [← hw, ← Category.assoc]
    have hId : e.inv.left ≫ e.hom.left = 𝟙 A' :=
      congrArg (fun k ↦ k.left) e.inv_hom_id
    rw [hId]
    exact Category.id_comp g
  exact he ▸ h

/-- 概要：矢の同型で right cofinality を移せる。
方針：両端の同型と元の cofinal な射を合成する。
規約：quasicategory 性や単射性は不要。
使われ方：反転を二度行った射を元の射へ戻す。 -/
lemma IsRightCofinal.of_arrow_iso {A B A' B' : SSet.{u}} {f : A ⟶ B} {g : A' ⟶ B'}
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal f) (e : Arrow.mk f ≅ Arrow.mk g) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal g := by
  let a := (Arrow.leftFunc.mapIso e).inv
  let b := (Arrow.rightFunc.mapIso e).hom
  have h := (isRightCofinal_of_isIso a).comp (hf.comp (isRightCofinal_of_isIso b))
  have he : a ≫ (f ≫ b) = g := by
    have hw : e.hom.left ≫ g = f ≫ e.hom.right := e.hom.w
    change e.inv.left ≫ (f ≫ e.hom.right) = g
    rw [← hw, ← Category.assoc]
    have hId : e.inv.left ≫ e.hom.left = 𝟙 A' :=
      congrArg (fun k ↦ k.left) e.inv_hom_id
    rw [hId]
    exact Category.id_comp g
  exact he ▸ h

/-- 概要：left cofinal な射の反転は right cofinal。
方針：左 anodyne・trivial Kan の因子分解を反転して十分性を使う。
規約：元の射に単射性を仮定しない。
使われ方：left 側の Quillen A を right 側へ移す。 -/
lemma IsLeftCofinal.op {A B : SSet.{u}} {f : A ⟶ B} (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal (SSet.opFunctor.map f) := by
  obtain ⟨M, i, p, _, hi, hp, he⟩ := hf.exists_anodyne_trivialKan_factorization
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p := hp
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_of_rightAnodyne _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalRightAnodyne_op_of_leftAnodyne i hi)).comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_of_trivialKanFibration (SSet.opFunctor.map p))
  rw [← Functor.map_comp, he] at h
  exact h

/-- 概要：right cofinal な射の反転は left cofinal。
方針：右 anodyne・trivial Kan の因子分解を反転して十分性を使う。
規約：元の始域・終域は任意。
使われ方：双対の判定を反転して戻す。 -/
lemma IsRightCofinal.op {A B : SSet.{u}} {f : A ⟶ B} (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal (SSet.opFunctor.map f) := by
  obtain ⟨M, i, p, _, hi, hp, he⟩ := hf.exists_anodyne_trivialKan_factorization
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p := hp
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isLeftCofinal_of_leftAnodyne _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalLeftAnodyne_op_of_rightAnodyne i hi)).comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isLeftCofinal_of_trivialKanFibration (SSet.opFunctor.map p))
  rw [← Functor.map_comp, he] at h
  exact h

/-- 概要：left cofinality は反転後の right cofinality と同値。
方針：両方向の反転と二重反転の矢の同型を使う。
規約：全ての単体集合の射に適用できる。
使われ方：Quillen A の双対化。 -/
lemma isLeftCofinal_iff_isRightCofinal_op {A B : SSet.{u}} (f : A ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal f ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal (SSet.opFunctor.map f) := by
  refine ⟨IsLeftCofinal.op, fun h ↦ ?_⟩
  exact h.op.of_arrow_iso (Arrow.isoMk (SSet.opFunctorCompOpFunctorIso.app A)
    (SSet.opFunctorCompOpFunctorIso.app B)
    ((SSet.opFunctorCompOpFunctorIso.hom.naturality f).symm))

/-- 概要：right cofinality は反転後の left cofinality と同値。
方針：両方向の反転と二重反転の矢の同型を使う。
規約：全ての単体集合の射に適用できる。
使われ方：right 側へ戻すときの判定。 -/
lemma isRightCofinal_iff_isLeftCofinal_op {A B : SSet.{u}} (f : A ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal f ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal (SSet.opFunctor.map f) := by
  refine ⟨IsRightCofinal.op, fun h ↦ ?_⟩
  exact h.op.of_arrow_iso (Arrow.isoMk (SSet.opFunctorCompOpFunctorIso.app A)
    (SSet.opFunctorCompOpFunctorIso.app B)
    ((SSet.opFunctorCompOpFunctorIso.hom.naturality f).symm))

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality
