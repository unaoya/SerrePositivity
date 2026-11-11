module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.LaxHomInputPathHomotopyOfFilling
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DerivedInputPathKanComplex
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomotopyInverseTransport
/-! # 指定境界充填から入力付き正本比較の同じ実逆射へ

概要：導来係数比較の既知の実逆射を、入力付き正本比較の実逆射として保持する。
方針：指定充填からの実ホモトピーを逆射で前後合成し、既知の両往復変形と合成する。
規約：逆射の選択は充填に依存せず、元入力と全 path を持つ比較を使う。
使われ方：④の充填から⑤の正本 Hom 比較へ進む際の入力付き模型の実逆射。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)

def dgGluingLaxHomInputPathInverse :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedCompositionInputPathComparison_equivalence R C D M X Y).choose

variable (hfill : ∃ T, (boundary 2).ι ≫ T =
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomDiagonalComparisonBoundary R C D M X Y)

def dgGluingLaxHomInputPathInverse_unitOfFilling :
    SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomInputPathComparison R C D M X Y ≫
      dgGluingLaxHomInputPathInverse R C D M X Y) (𝟙 _) := by
  let H := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomInputPathComparisonHomotopyOfFilling R C D M X Y
    hfill.choose hfill.choose_spec
  have hinv := Classical.choose_spec
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedCompositionInputPathComparison_equivalence R C D M X Y)
  let η := hinv.1.some
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomotopyInverseTransportUnit H
    (dgGluingLaxHomInputPathInverse R C D M X Y) η

def dgGluingLaxHomInputPathInverse_counitOfFilling :
    SSet.Homotopy (dgGluingLaxHomInputPathInverse R C D M X Y ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomInputPathComparison R C D M X Y) (𝟙 _) := by
  letI := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedCompositionInputPathPullback_kanComplex R C D M X Y
  let H := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomInputPathComparisonHomotopyOfFilling R C D M X Y
    hfill.choose hfill.choose_spec
  have hinv := Classical.choose_spec
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedCompositionInputPathComparison_equivalence R C D M X Y)
  let ε := hinv.2.some
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomotopyInverseTransportCounit H
    (dgGluingLaxHomInputPathInverse R C D M X Y) ε

include hfill in
lemma dgGluingLaxHomInputPathComparison_equivalence_of_filling :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomInputPathComparison R C D M X Y) :=
  ⟨dgGluingLaxHomInputPathInverse R C D M X Y,
    ⟨dgGluingLaxHomInputPathInverse_unitOfFilling R C D M X Y hfill⟩,
    ⟨dgGluingLaxHomInputPathInverse_counitOfFilling R C D M X Y hfill⟩⟩
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
