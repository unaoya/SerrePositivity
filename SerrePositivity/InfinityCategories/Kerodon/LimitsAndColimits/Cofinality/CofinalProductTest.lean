module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.ProductTestFibration

/-!
概要：積の射影への相対関手空間と通常の内部 Hom の厳密な同型。
方針：第一射影を忘却に、底図式との対を逆射に使う。
規約：この同型には Kan 性や quasicategory 性は不要。
使われ方：Kerodon Proposition 7.2.1.5（Tag 02N5） の cofinal ⇒ 弱同値。

対応節は Kerodon 7.2（Tag 02MZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality

/-- 概要：固定した関手頂点への定値族の uncurry は底の射を復元する。
方針：内部 Hom の評価と恒等射による引き戻しを各次数で計算する。
規約：F1.FunctorFiber の同じ一般計算を import 範囲を狭めて証明する。
使われ方：積の射影への相対関手の底条件。 -/
lemma cofinalUncurry_const_functorVertex {A L B : SSet.{u}} (f : A ⟶ B) :
    uncurry (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) : L ⟶ (ihom A).obj B) = fst A L ≫ f := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  dsimp [uncurry, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex, curry', curry, SSet.unitHomEquiv, SSet.const]
  rfl

/-- 概要：積の射影への相対関手空間は第一因子への関手空間と同型。
方針：第一射影で忘却し、評価と指定底図式の対を curry して逆射にする。
規約：底図式 a は任意。
使われ方：cofinality の定義に使う検査を通常の写像空間へ移す。 -/
def cofinalProductTestIso {A B : SSet.{u}} (a : A ⟶ B) (Z : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalFunctorSpace (snd Z B) a ≅ (ihom A).obj Z := by
  let ι := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom A).map (snd Z B)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a)
  let q := ι ≫ (ihom A).map (fst Z B)
  let g := curry (lift ((ihom.ev A).app Z) (fst A ((ihom A).obj Z) ≫ a))
  have hg : g ≫ (ihom A).map (snd Z B) = SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a) := by
    apply uncurry_injective
    rw [uncurry_natural_right, uncurry_curry]
    simp only [CategoryTheory.Functor.id_obj, lift_snd, cofinalUncurry_const_functorVertex]
  let j := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift _ _ g hg
  refine { hom := q, inv := j, hom_inv_id := ?_, inv_hom_id := ?_ }
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext ((ihom A).map (snd Z B)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a)
    change (q ≫ j) ≫ ι = ι
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι]
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry]
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, lift_fst]
      change uncurry (ι ≫ (ihom A).map (fst Z B)) = uncurry ι ≫ fst Z B
      exact uncurry_natural_right ι (fst Z B)
    · simp only [CategoryTheory.Functor.id_obj, Category.assoc, lift_snd]
      rw [← Category.assoc, whiskerLeft_fst]
      have hb := congrArg uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp ((ihom A).map (snd Z B)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a))
      rw [uncurry_natural_right, cofinalUncurry_const_functorVertex] at hb
      exact hb.symm
  · change (j ≫ ι) ≫ (ihom A).map (fst Z B) = 𝟙 _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι]
    apply uncurry_injective
    rw [uncurry_natural_right, uncurry_curry, lift_fst, uncurry_id_eq_ev]

/-- 概要：積の検査同型は始域の前合成と可換。
方針：fiber の包含後の制限の計算則と内部 Hom の自然性を使う。
規約：i と底図式 a は任意。
使われ方：cofinal な制限写像を元の前合成そのものと同定する。 -/
lemma cofinalProductTestIso_pre {A D B : SSet.{u}} (a : A ⟶ B) (i : D ⟶ A)
    (Z : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalFunctorPre (snd Z B) a i ≫ (cofinalProductTestIso (i ≫ a) Z).hom =
      (cofinalProductTestIso a Z).hom ≫ (pre i).app Z := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalFunctorPre (snd Z B) a i ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι _ _ ≫ (ihom D).map (fst Z B)) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι _ _ ≫ (ihom A).map (fst Z B)) ≫ (pre i).app Z
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalFunctorPre_ι, Category.assoc, ← (pre i).naturality (fst Z B)]
  exact (Category.assoc _ _ _).symm

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality
