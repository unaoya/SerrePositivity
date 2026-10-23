module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.IntervalReplacementContractionEndpoints
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.HomotopyIsoRawComparison
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.HomotopyIsoWhiskering

/-!
概要：元の定値切断の後の入力射影から恒等射への、指定 path を保持する同型を構成する。
方針：同じ形状収縮を円柱として読み、終点では元の canonical path を厳密に回収する。
規約：元の切断・元の path を保持。使われ方：native 比較と模型比較の左脚の同型。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {X Y : SSet.{u}} [KanComplex Y] (f : X ⟶ Y)
local notation "P" => intervalReplacement f
local notation "pa" => pullback.fst (NatTrans.app (intervalEndpointNatTrans 0) Y) f
local notation "pr" => pullback.snd (NatTrans.app (intervalEndpointNatTrans 0) Y) f

/-- 元の定値切断から元の置換の恒等射への、入力を固定した指定円柱。 -/
def intervalReplacementSectionHomotopy :
    SSet.Homotopy (pr ≫ intervalReplacementSection f) (𝟙 P) where
  h := intervalReplacementContraction f
  h₀ := intervalReplacementContraction_zero f
  h₁ := intervalReplacementContraction_one f
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 置換内の指定円柱の終点像は、元の全 path 円柱に厳密に一致する。 -/
lemma intervalReplacementSectionHomotopy_endpoint :
    (intervalReplacementSectionHomotopy f).h ≫ intervalReplacementEndpoint f =
      (intervalReplacementCanonicalPathHomotopy f).h := by
  change intervalReplacementContraction f ≫ (pa ≫ (intervalEndpointNatTrans 1).app Y) = _
  rw [← Category.assoc, intervalReplacementContraction_path]
  change curry (intervalShapeContraction P ≫ uncurry pa) ≫ evaluateFunctorAt _ = _
  rw [curry_evaluateFunctorAt_interval, ← Category.assoc, intervalShapeContraction_path_one]
  rfl

/-- Kan 入力では元の指定円柱は定値切断と恒等射の間の指定関手同型を与える。 -/
def intervalReplacementSectionIso [KanComplex X] :
    FunctorIso (pr ≫ intervalReplacementSection f) (𝟙 P) :=
  functorIsoOfSimplicialHomotopy (intervalReplacementSectionHomotopy f)

/-- この指定同型の終点像は、明示した端点の表示の下で元の path の指定類である。 -/
lemma intervalReplacementSectionIso_endpoint [KanComplex X] :
    HEq ((intervalReplacementSectionIso f).postcomp (intervalReplacementEndpoint f))
      (intervalReplacementPathIso f) := by
  have hi := homotopyIso_heq_of_h_eq
    (functorHomotopyPostcomp (intervalReplacementSectionHomotopy f)
      (intervalReplacementEndpoint f)) (intervalReplacementCanonicalPathHomotopy f)
    (intervalReplacementSectionHomotopy_endpoint f)
  rw [homotopyIso_postcomp] at hi
  have he : functorIsoOfSimplicialHomotopy (intervalReplacementCanonicalPathHomotopy f) =
      intervalReplacementPathIso f := by
    apply Iso.ext
    rfl
  exact hi.trans (heq_of_eq he)

end SerrePositivity.InfinityCategories.F2
