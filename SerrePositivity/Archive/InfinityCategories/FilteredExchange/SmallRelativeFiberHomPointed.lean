module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentFiberPointedSourceIso
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SmallRelativeSourceRestriction
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeFiberRestriction

/-!
概要：縮小後の fiber Hom の持ち上げと、元の大きい全空間の pointed 成分を厳密に照合する。
方針：相対関手の宇宙移送と fiber 同型の同じ全次数の値を計算する。
規約：元の相対射と全パラメータを保持。使われ方：旧 prism 出力と新しい終点評価の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B C : SSet.{u}}
  (J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (a : C ⟶ B) (b : B _⦋0⦌) (ha : a = SSet.const b)
local notation "pJ" => smallLeftUnstraighteningProjection J
local notation "Q" => relativeFunctorBaseFiberHom pJ a b ha
local notation "E" => uliftFunctorSpaceIso C (vertexFiber pJ b)

/-- 同じ全相対族の fiber Hom を持ち上げて含めると、元の全空間の同じ pointed 成分になる。 -/
lemma smallRelativeFiberHom_pointed :
    uncurry ((SSet.uliftFunctor.{u + 1, u}).map Q ≫ (E).hom) ≫
      coherentCospanFiberPointedSource J b =
      relativeFunctorUncurry (smallUnstraighteningSourceRelativeIso J a).hom ≫
        pullback.fst pointedSpaceProjection J := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨⟨x⟩, ⟨h⟩⟩
  rfl

end SerrePositivity.InfinityCategories.F2
