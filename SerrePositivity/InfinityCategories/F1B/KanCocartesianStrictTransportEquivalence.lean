module

public import SerrePositivity.InfinityCategories.F1B.KanCocartesianStrictTransport
public import SerrePositivity.InfinityCategories.F1B.KanInitialSectionLifting
public import SerrePositivity.InfinityCategories.F1B.KanNerveInitialPrism

/-!
概要：一般の cocartesian strict transport の各値を元の fiber と比較する。
方針：undercategory の恒等射からの固定始点収縮を、section の評価の全境界持ち上げへ渡す。
規約：比較射は構成済みの恒等射での評価そのもの。
使われ方：一般の scaffold の fiber 比較と kanFiberwiseHom の cartesian fibration 性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：評価の標的となる頂点 fiber は quasicategory。
方針：inner fibration の頂点 fiber の充填性を使う。
規約：このファイル内の同値の型のための局所 instance。
使われ方：strict transport の評価の ∞ 圏的な比較。 -/
local instance {E B : SSet.{u}} (p : E ⟶ B) [InnerFibration p] (v : B _⦋0⦌) :
    Quasicategory (vertexFiber p v) := vertexFiber_quasicategory_of_innerFibration p v

/-- 概要：cocartesian strict transport の恒等射評価は自明 Kan fibration。
方針：under の恒等射が通常の始対象であることから固定収縮を取り、相対輸送を適用する。
規約：元の p は left fibration でなく一般の cocartesian fibration でよい。
使われ方：strict transport の fiber の比較と section の選択の高次一意性。 -/
instance kanCocartesianStrictTransportEvaluate_trivialKanFibration
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [CocartesianFibration p] (c : C) :
    TrivialKanFibration (kanCocartesianStrictTransportEvaluate p c) := by
  exact kanCocartesianSectionsEvaluate_trivialKanFibration_of_fixedPrism p
    (nerveMap (Under.forget c)) (nerveVertex (Under.mk (𝟙 c)))
    (exists_kanNerveInitialPrism (Under.mkIdInitial (X := c)))

/-- 概要：strict transport の恒等射評価は ∞ 圏の同値。
方針：評価射の自明 Kan fibration 性に同値判定を適用する。
規約：各値は cocartesian section の全部分 ∞ 圏。
使われ方：Cat 値 strict transport の各値の実際の fiber との同定。 -/
lemma kanCocartesianStrictTransportEvaluate_isQCatEquivalence
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [CocartesianFibration p] (c : C) :
    IsQCatEquivalence (kanCocartesianStrictTransportEvaluate p c) :=
  isQCatEquivalence_of_trivialKanFibration _

/-- 概要：cocartesian strict transport の値と元の fiber の間の明示的な ∞ 圏同値。
方針：恒等射評価の同値性から逆射と自然同値を選ぶ。
規約：順方向の関手は恒等射での評価。
使われ方：一般の scaffold の各 fiber の比較。 -/
def kanCocartesianStrictTransportFiberEquivalence
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [CocartesianFibration p] (c : C) :
    QCatEquivalence (kanCocartesianStrictTransport p c) (vertexFiber p (nerveVertex c)) :=
  (kanCocartesianStrictTransportEvaluate_isQCatEquivalence p c).choose

/-- 概要：評価で指定した値を持つ cocartesian section の選択空間は可縮な Kan 複体。
方針：自明 Kan fibration の頂点 fiber の可縮性を使う。
規約：指定した値は元の fibration の c 上の頂点。
使われ方：section の存在と高次の一意性を同時に保持する比較。 -/
lemma kanCocartesianStrictTransportEvaluate_fiber_isContractibleKan
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [CocartesianFibration p] (c : C)
    (e : (vertexFiber p (nerveVertex c)) _⦋0⦌) :
    IsContractibleKan (vertexFiber (kanCocartesianStrictTransportEvaluate p c) e) :=
  vertexFiber_isContractibleKan _ e

end SerrePositivity.InfinityCategories
