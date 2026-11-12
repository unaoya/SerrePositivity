module
public import SerrePositivity.KST.SConstruction.PointwisePushoutApex

/-! # 点ごとの押し出しと図式の角での評価
概要：C 内の同じ押し出し選択の各角は、評価した span の押し出しである。
方針：curry の評価と span・図式の座標交換を照合する。
規約：選択の保存を追加仮定にしない。使われ方：ρ の subobject と quotient の厳密回収。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：座標交換した span の族の角での制限は、角で評価した元の span の curry。
方針：二回 uncurry して積の座標を計算する。
規約：任意の形状の任意の頂点。使われ方：同じ C 内の押し出し選択の回収。 -/
lemma exchangeDiagramFamily_evaluate {A B K C : SSet.{u}}
    (F : A ⊗ K ⟶ (ihom B).obj C) (b : B _⦋0⦌) :
    lift (SSet.const b) (𝟙 K) ≫ exchangeDiagramFamily F =
      curry (F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt b) := by
  apply uncurry_injective
  rw [uncurry_natural_left, exchangeDiagramFamily, uncurry_curry, uncurry_curry]
  rw [← Category.assoc]
  have he : (A ◁ lift (SSet.const b) (𝟙 K)) ≫ exchangeFirstTwo A B K =
      lift (SSet.const b) (𝟙 (A ⊗ K)) := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro v
    rfl
  rw [he, ← curry_evaluate_vertex, curry_uncurry]

/-- 概要：元の C 内の図式の押し出し頂点の角は評価した span の押し出し頂点。
方針：curry の評価と同じ選択の前合成の自然性。
規約：同型に弱めない。使われ方：ρ の各角の正規化。 -/
lemma pointwiseDiagramPushoutApex_evaluate {B K C : SSet.{u}}
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (F : (horn 2 0 : SSet.{u}) ⊗ K ⟶ (ihom B).obj C) (b : B _⦋0⦌) :
    pointwiseDiagramPushoutApex F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt b =
      pointwisePushoutApex (curry (F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt b)) := by
  rw [pointwiseDiagramPushoutApex, curry_evaluate_vertex, ← pointwisePushoutApex_pre,
    exchangeDiagramFamily_evaluate]

/-- 概要：恒等な枝を持つ span を curry すると標準の恒等 span の族。
方針：前合成を内部 Hom に移す。
規約：二つの向きで同じ公式。使われ方：正規化した押し出し頂点の計算。 -/
lemma curry_identitySpan {K C : SSet.{u}} (b : Bool)
    (L : (Δ[1] : SSet.{u}) ⊗ K ⟶ C) :
    curry ((identitySpanShape b ▷ K) ≫ L) = curry L ≫ identitySpanFamily b C := by
  apply uncurry_injective
  rw [uncurry_curry, identitySpanFamily, uncurry_pre_app, uncurry_curry]

end SerrePositivity.KST.SConstruction
