module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardComposition
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.FunctorMapping

/-! # 厳密 dg 関手の標準 DK Hom 上の作用
概要：元の dg 関手を標準 DK Hom の全単体に作用させ、全ての面と退化を保つ。
方針：全有限部分集合の成分に同じ Hom chain map を適用し、標準削除和を移送する。
規約：閉零単体だけに制限しない。使われ方：dg 関手圏の単体的関手化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]
  {E : Type w} [_root_.SerrePositivity.DifferentialGraded.DGCategory A E]

/-- 元の Hom chain map による、標準 DK 成分族の像。 -/
def dgStandardDataMap (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D E) {x y : D} {n : ℕ}
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y n) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A (F.obj x) (F.obj y) n :=
  fun i => (F.map x y).f i.val.2 (f i)

/-- 成分族の像は、指定した元の斉次成分の像を回収する。 -/
lemma dgStandardDataMap_component (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D E) {x y : D} {n : ℕ}
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y n) (J : Finset (Fin (n + 1))) (k : ℤ)
    (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    (dgStandardDataMap F f).component J k hJ hk =
      (F.map x y).f k (f.component J k hJ hk) := rfl

/-- 元の Hom chain map は、標準削除和の全項を保つ。 -/
lemma dgStandardDataMap_rhs (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D E) {x y : D} {n : ℕ}
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y n) (J : Finset (Fin (n + 1))) (k : ℤ)
    (hk : k = 1 - (J.card : ℤ)) :
    (F.map x y).f (k + 1) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardRhs f J k hk) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardRhs (dgStandardDataMap F f) J k hk := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardRhs
  split_ifs
  · simp only [map_sum, map_zsmul, dgStandardDataMap_component]
  · exact map_zero _

/-- 標準 DK 単体の全次数方程式を保つ、元の厳密 dg 関手の作用。 -/
def dgStandardSimplexMap (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D E) {x y : D} {n : ℕ}
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex A x y n) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex A (F.obj x) (F.obj y) n :=
  ⟨dgStandardDataMap F f.val, by
    intro J k hJ hk
    rw [dgStandardDataMap_component, ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.map_differential,
      f.property J k hJ hk, dgStandardDataMap_rhs]⟩

/-- 全標準単体の像は、面と退化を含む全引き戻しと可換。 -/
lemma dgStandardSimplexMap_pullback (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D E) {x y : D} {m n : ℕ}
    (α : Fin (m + 1) →o Fin (n + 1)) (f : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex A x y n) :
    dgStandardSimplexMap F (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardPullback α f) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardPullback α (dgStandardSimplexMap F f) := by
  apply Subtype.ext
  change dgStandardDataMap F (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardPullback α f).val =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardPullback α (dgStandardSimplexMap F f)).val
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardPullback_val, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardPullback_val]
  funext i
  simp only [dgStandardDataMap, dgStandardSimplexMap, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.component, LinearMap.coe_mk, AddHom.coe_mk]
  split_ifs
  · rfl
  · exact map_zero _

/-- 厳密 dg 関手による標準 DK Hom の元の単体集合の射。 -/
def dgStandardHomMap (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D E) (x y : D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := A) x y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := A) (F.obj x) (F.obj y) where
  app n := ↾fun f => dgStandardSimplexMap F f
  naturality := by
    intro m n α
    apply ConcreteCategory.hom_ext
    intro f
    exact dgStandardSimplexMap_pullback F α.unop.toOrderHom f

end SerrePositivity.KST.SConstruction
