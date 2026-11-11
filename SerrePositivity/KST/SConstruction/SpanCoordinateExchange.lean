module
public import SerrePositivity.KST.SConstruction.SpanPrisms
public import SerrePositivity.KST.SConstruction.DiagramPushoutChoice

/-! # span と図式の座標の交換
概要：span の族の値が更に図式であるとき、元の C 内の span の族へ並べ替える。
方針：二つの先頭因子の交換と curry を使う。
規約：添字の制限と厳密に両立する。使われ方：C 内の点ごとの押し出しによる ρ。
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

/-- 概要：三因子のうち先頭二因子だけを交換する。
方針：結合子と braiding を合成する。
規約：第三因子を固定する。使われ方：cofiber 正方形と押し出し span の座標交換。 -/
def exchangeFirstTwo (A B K : SSet.{u}) : A ⊗ (B ⊗ K) ⟶ B ⊗ (A ⊗ K) :=
  (α_ A B K).inv ≫ ((β_ A B).hom ▷ K) ≫ (α_ B A K).hom

/-- 概要：先頭二因子の交換は第三因子の射と可換。
方針：各単体の三つ組で両合成を計算する。
規約：第三因子の射は任意。使われ方：ρ の添字制限の自然性。 -/
lemma exchangeFirstTwo_naturality (A B : SSet.{u}) {L K : SSet.{u}} (i : L ⟶ K) :
    (A ◁ (B ◁ i)) ≫ exchangeFirstTwo A B K =
      exchangeFirstTwo A B L ≫ (B ◁ (A ◁ i)) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  rfl

/-- 概要：図式を値とする span の族を、元の標的での span の族に交換する。
方針：uncurry して二つの先頭因子を交換し、span 方向で curry する。
規約：一般の形状 A,B を許す。使われ方：C 内での正規化した押し出しの入力。 -/
def exchangeDiagramFamily {A B K C : SSet.{u}} (F : A ⊗ K ⟶ (ihom B).obj C) :
    B ⊗ K ⟶ (ihom A).obj C :=
  curry (exchangeFirstTwo A B K ≫ uncurry F)

/-- 概要：図式の族の座標交換は第三因子の前合成と可換。
方針：uncurry の自然性と因子交換の自然性。
規約：全てのパラメーターで厳密な等号。使われ方：ρ の面・退化との両立。 -/
lemma exchangeDiagramFamily_pre {A B K L C : SSet.{u}}
    (F : A ⊗ K ⟶ (ihom B).obj C) (i : L ⟶ K) :
    exchangeDiagramFamily ((A ◁ i) ≫ F) = (B ◁ i) ≫ exchangeDiagramFamily F := by
  apply uncurry_injective
  rw [exchangeDiagramFamily, uncurry_curry, uncurry_natural_left,
    exchangeDiagramFamily, uncurry_natural_left, uncurry_curry]
  rw [← Category.assoc, ← exchangeFirstTwo_naturality, Category.assoc]

/-- 概要：先頭二因子の交換は第一因子の射と可換。
方針：各単体の三つ組で両合成を計算する。
規約：第一因子の射は任意。使われ方：恒等 span の座標交換。 -/
lemma exchangeFirstTwo_naturality_left {A A' : SSet.{u}} (i : A' ⟶ A) (B K : SSet.{u}) :
    (i ▷ (B ⊗ K)) ≫ exchangeFirstTwo A B K =
      exchangeFirstTwo A' B K ≫ (B ◁ (i ▷ K)) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  rfl

/-- 概要：図式の族の第一形状の制限は交換後の前合成となる。
方針：uncurry の自然性と因子交換の自然性。
規約：射の厳密な等号。使われ方：正規化された恒等 span への制限。 -/
lemma exchangeDiagramFamily_pre_left {A A' B K C : SSet.{u}}
    (F : A ⊗ K ⟶ (ihom B).obj C) (i : A' ⟶ A) :
    exchangeDiagramFamily ((i ▷ K) ≫ F) = exchangeDiagramFamily F ≫ (pre i).app C := by
  apply uncurry_injective
  rw [exchangeDiagramFamily, uncurry_curry, uncurry_natural_left, uncurry_pre_app,
    exchangeDiagramFamily, uncurry_curry]
  rw [← Category.assoc, ← exchangeFirstTwo_naturality_left, Category.assoc]

/-- 概要：区間の族を交換して端点で評価すると元の族の端点の uncurry。
方針：curry の端点評価と因子交換を各単体で照合する。
規約：両端点に共通の公式。使われ方：正規化した押し出し頂点の回収。 -/
lemma exchangeDiagramFamily_evaluation_interval {B K C : SSet.{u}}
    (F : (Δ[1] : SSet.{u}) ⊗ K ⟶ (ihom B).obj C) (i : Fin 2) :
    exchangeDiagramFamily F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm i) =
      uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i K ≫ F) := by
  rw [exchangeDiagramFamily, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval, uncurry_natural_left]
  rw [← Category.assoc]
  congr 1

end SerrePositivity.KST.SConstruction
