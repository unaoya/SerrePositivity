module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.ScaffoldPullbackMarkedCore
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.KanSquareFiberEquivalence

/-!
概要：同じ境界値を固定した元の辺保存 Hom と scaffold Hom の core の比較同値。
方針：実際の自然な正方形を指定値の fiber に制限し、全空間と底の同値を使う。
規約：境界は任意の単射な部分底であり、その充填性を仮定しない。
使われ方：セル貼合せの元の native Hom の相対比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
attribute [local instance] vertexFiber_kanComplex_of_leftFibration
variable {C : Type u} [Category.{u} C] {E F : SSet.{u}}
  (p : E ⟶ nerve C) [CocartesianFibration p] (q : F ⟶ nerve C)
  [CocartesianFibration q] {a b : Over (nerve C)} (f : a ⟶ b)
  (r : (quasicategoryCore (cocartesianPullbackHomSpace p q a) : SSet.{u}) _⦋0⦌)

local instance (z : Over (nerve C)) : Quasicategory (cocartesianPullbackHomSpace p q z) :=
  inferInstanceAs (Quasicategory (markedCocartesianFunctorSpace q
    (pullback.snd z.hom p ≫ p) {e | IsCocartesianEdge (pullback.fst z.hom p) e}))

local instance (z : Over (nerve C)) :
    Quasicategory (cocartesianScaffoldPullbackMarkedHom p q z) :=
  inferInstanceAs (Quasicategory (markedCocartesianFunctorSpace q _
    (cocartesianScaffoldPullbackMark p z)))

local instance [Mono f.left] :
    Fibration (quasicategoryCoreMap (cocartesianPullbackHomPre p q f)) :=
  core_cocartesianPullbackHomPre_fibration p q f

local instance [Mono f.left] :
    Fibration (cocartesianScaffoldPullbackMarkedCoreRestriction p q f) :=
  cocartesianScaffoldPullbackMarkedCoreRestriction_fibration p q f

/-- 同じ scaffold 比較を、指定された元の境界値の fiber へ制限する。 -/
def cocartesianScaffoldPullbackBoundaryFiberPre :=
  kanSquareFiberMap (quasicategoryCoreMap (cocartesianPullbackHomPre p q f))
    (cocartesianScaffoldPullbackMarkedCoreRestriction p q f)
    (cocartesianScaffoldPullbackMarkedCorePre p q b)
    (cocartesianScaffoldPullbackMarkedCorePre p q a)
    (cocartesianScaffoldPullbackMarkedCorePre_naturality p q f) r

/-- 指定境界 fiber の同じ比較は、元の core 前合成そのものを保持する。 -/
lemma cocartesianScaffoldPullbackBoundaryFiberPre_ι :
    cocartesianScaffoldPullbackBoundaryFiberPre p q f r ≫
      vertexFiberι (cocartesianScaffoldPullbackMarkedCoreRestriction p q f)
        ((cocartesianScaffoldPullbackMarkedCorePre p q a).app (Opposite.op ⦋0⦌) r) =
    vertexFiberι (quasicategoryCoreMap (cocartesianPullbackHomPre p q f)) r ≫
      cocartesianScaffoldPullbackMarkedCorePre p q b :=
  kanSquareFiberMap_ι _ _ _ _ _ _

/-- 任意の単射な部分底で、元の指定境界値の同じ fiber 比較は同値。 -/
lemma cocartesianScaffoldPullbackBoundaryFiberPre_isQCatEquivalence [Mono f.left] :
    IsQCatEquivalence (cocartesianScaffoldPullbackBoundaryFiberPre p q f r) := by
  exact kanSquareFiberMap_isQCatEquivalence _ _ _ _ _ r
    (cocartesianScaffoldPullbackMarkedCorePre_isQCatEquivalence p q b)
    (cocartesianScaffoldPullbackMarkedCorePre_isQCatEquivalence p q a)

end SerrePositivity.InfinityCategories
