module
public import SerrePositivity.KST.SConstruction.SpanCoordinateExchange

/-! # 点ごとの正規化した押し出しの頂点
概要：C 内の span の族を、同じ正規化した選択による押し出し頂点の族へ送る。
方針：選んだ四角形の (1,1) を評価する。
規約：パラメーターごとの別の選択はしない。使われ方：McCarthy の ρ の元の C 内での構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：span の族の点ごとの押し出し頂点を取る。
方針：正規化した選択で正方形を作って右上の頂点を評価する。
規約：C 内の同じ選択を全パラメーターに使う。使われ方：ρ の各角と Ar の各区間の値。 -/
def pointwisePushoutApex {K C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (d : K ⟶ (ihom (horn 2 0 : SSet.{u})).obj C) : K ⟶ C :=
  chosenPushoutFamily d ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
    (stdSimplex.obj₀Equiv.symm (1 : Fin 2), stdSimplex.obj₀Equiv.symm (1 : Fin 2))

/-- 概要：点ごとの押し出し頂点の族は任意のパラメーターの制限と可換。
方針：固定した選択と頂点評価への後合成。
規約：厳密な等号。使われ方：ρ の単体恒等式。 -/
lemma pointwisePushoutApex_pre {K L C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (d : K ⟶ (ihom (horn 2 0 : SSet.{u})).obj C) (i : L ⟶ K) :
    pointwisePushoutApex (i ≫ d) = i ≫ pointwisePushoutApex d :=
  (Category.assoc _ _ _).trans (Category.assoc _ _ _)

/-- 概要：二重の図式の span を点ごとに押し出し、元の図式の族に戻す。
方針：span と図式の座標を交換し、C 内の押し出し頂点を取って curry する。
規約：cofiber 図式の圏内で新たな押し出しを選ばない。使われ方：ρ の元の正方形の族。 -/
def pointwiseDiagramPushoutApex {B K C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (F : (horn 2 0 : SSet.{u}) ⊗ K ⟶ (ihom B).obj C) : K ⟶ (ihom B).obj C :=
  curry (pointwisePushoutApex (exchangeDiagramFamily F))

/-- 概要：点ごとの図式の押し出し頂点は任意の添字制限と可換。
方針：座標交換・押し出し頂点・curry の自然性。
規約：全ての面と退化を含む。使われ方：ρ の単体的自然性。 -/
lemma pointwiseDiagramPushoutApex_pre {B K L C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (F : (horn 2 0 : SSet.{u}) ⊗ K ⟶ (ihom B).obj C) (i : L ⟶ K) :
    pointwiseDiagramPushoutApex (((horn 2 0 : SSet.{u}) ◁ i) ≫ F) =
      i ≫ pointwiseDiagramPushoutApex F := by
  rw [pointwiseDiagramPushoutApex, exchangeDiagramFamily_pre, pointwisePushoutApex_pre,
    curry_natural_left]
  rfl

/-- 概要：恒等な枝を持つ標準 span の点ごとの押し出し頂点は元の辺の終点。
方針：同時正規化した押し出し選択と頂点評価の式。
規約：二つの向きで同じ選択を使う。使われ方：ρ の時刻零の回収。 -/
lemma pointwisePushoutApex_identity {K C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (b : Bool) (g : K ⟶ (ihom (Δ[1] : SSet.{u})).obj C) :
    pointwisePushoutApex (g ≫ identitySpanFamily b C) =
      g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
  simp only [pointwisePushoutApex, chosenPushoutFamily, Category.assoc]
  rw [← Category.assoc (identitySpanFamily b C),
    normalizedPushoutSquareChoice_identity, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.stable_pre_evaluateFunctorAt]
  cases b <;> rfl

/-- 概要：一方の枝が恒等な図式の span の点ごとの押し出し頂点は元の辺の終点の図式。
方針：座標交換後の恒等 span の正規化と端点評価を合わせる。
規約：元の図式の全高次単体を厳密に回収する。使われ方：ρ の恒等射側の端点。 -/
lemma pointwiseDiagramPushoutApex_identity {B K C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (b : Bool) (F : (Δ[1] : SSet.{u}) ⊗ K ⟶ (ihom B).obj C) :
    pointwiseDiagramPushoutApex ((identitySpanShape b ▷ K) ≫ F) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K ≫ F := by
  apply uncurry_injective
  rw [pointwiseDiagramPushoutApex, uncurry_curry, exchangeDiagramFamily_pre_left]
  change pointwisePushoutApex (exchangeDiagramFamily F ≫ identitySpanFamily b C) = _
  rw [pointwisePushoutApex_identity, exchangeDiagramFamily_evaluation_interval]

end SerrePositivity.KST.SConstruction
