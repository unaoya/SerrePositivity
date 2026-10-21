module

public import SerrePositivity.InfinityCategories.F1.CocartesianScaffoldPullbackNativeCore
public import SerrePositivity.InfinityCategories.F1.CocartesianScaffoldPullbackBoundaryFiber

/-!
概要：元の native Hom の指定境界値の延長空間と同じ scaffold の相対 Hom の同値。
方針：元の native 制限と同じ比較の自然な正方形を実際の fiber に制限する。
規約：始域は両射影を引き戻した元の全 cocartesian Hom の core。
使われ方：セル貼合せの元の native 延長空間の局所比較。
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
  (r : (quasicategoryCore
    (cocartesianRelativeFunctorSpace (pullback.fst a.hom p) (pullback.fst a.hom q)) :
      SSet.{u}) _⦋0⦌)

local instance (z : Over (nerve C)) : InnerFibration (pullback.fst z.hom q) :=
  ⟨innerFibrations.pullback_fst z.hom q (InnerFibration.mem (q := q))⟩

local instance (z : Over (nerve C)) :
    Quasicategory (cocartesianScaffoldPullbackMarkedHom p q z) :=
  inferInstanceAs (Quasicategory (markedCocartesianFunctorSpace q _
    (cocartesianScaffoldPullbackMark p z)))

local instance [Mono f.left] :
    Fibration (quasicategoryCoreMap (cocartesianPullbackNativePre p q f)) :=
  core_cocartesianPullbackNativePre_fibration p q f

local instance [Mono f.left] :
    Fibration (cocartesianScaffoldPullbackMarkedCoreRestriction p q f) :=
  cocartesianScaffoldPullbackMarkedCoreRestriction_fibration p q f

/-- 同じ native Hom の指定境界値を固定した、同じ scaffold の比較。 -/
def cocartesianScaffoldPullbackNativeBoundaryPre :=
  kanSquareFiberMap (quasicategoryCoreMap (cocartesianPullbackNativePre p q f))
    (cocartesianScaffoldPullbackMarkedCoreRestriction p q f)
    (cocartesianScaffoldPullbackNativeCorePre p q b)
    (cocartesianScaffoldPullbackNativeCorePre p q a)
    (cocartesianScaffoldPullbackNativeCorePre_naturality p q f) r

/-- 同じ native 延長空間の比較は、元の native core 比較を厳密に保持する。 -/
lemma cocartesianScaffoldPullbackNativeBoundaryPre_ι :
    cocartesianScaffoldPullbackNativeBoundaryPre p q f r ≫
      vertexFiberι (cocartesianScaffoldPullbackMarkedCoreRestriction p q f)
        ((cocartesianScaffoldPullbackNativeCorePre p q a).app (Opposite.op ⦋0⦌) r) =
    vertexFiberι (quasicategoryCoreMap (cocartesianPullbackNativePre p q f)) r ≫
      cocartesianScaffoldPullbackNativeCorePre p q b :=
  kanSquareFiberMap_ι _ _ _ _ _ _

/-- 任意の単射な部分底で、元の native 延長空間からの同じ相対比較は同値。 -/
lemma cocartesianScaffoldPullbackNativeBoundaryPre_isQCatEquivalence [Mono f.left] :
    IsQCatEquivalence (cocartesianScaffoldPullbackNativeBoundaryPre p q f r) :=
  kanSquareFiberMap_isQCatEquivalence _ _ _ _ _ r
    (cocartesianScaffoldPullbackNativeCorePre_isQCatEquivalence p q b)
    (cocartesianScaffoldPullbackNativeCorePre_isQCatEquivalence p q a)

end SerrePositivity.InfinityCategories
