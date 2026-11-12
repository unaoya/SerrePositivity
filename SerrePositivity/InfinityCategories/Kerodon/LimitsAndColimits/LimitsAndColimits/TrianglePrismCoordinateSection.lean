module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleLabelCoordinateSection
public import Mathlib.AlgebraicTopology.SimplicialSet.ProdStdSimplex

/-!
概要：native path の二座標から標準区間と標準単体を同時に回収する。
方針：有限 path の切断を nerve に移し、零側の添字包含を切り詰めて戻す。
規約：次数ごとの厳密な切断であり、全 K の単射 encoder の存在は含めない。
使われ方：固定した K 頂点上での全高次パラメーターの回収。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 零側の n+1 頂点を残す単調な切り詰め。 -/
def trianglePrismRetraction (n : ℕ) : Fin (n + 3) →o Fin (n + 1) where
  toFun i := ⟨min i.val n, by omega⟩
  monotone' := by
    intro i j hij
    exact min_le_min_right n hij

/-- 区間と標準単体の頂点の組を、二座標を持つ native path へ送る関手。 -/
def trianglePrismCoordinateFunctor (n : ℕ) :
    ULift.{u} (Fin 2 × Fin (n + 1)) ⥤
      Path (ULift.up (0 : Fin (n + 3)) : ULift.{u} (Fin (n + 3)))
        (ULift.up (Fin.last (n + 2))) where
  obj p := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.trianglePrismCoordinatePath n p.down.1 p.down.2
  map h := ⟨⟨⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.trianglePrismCoordinatePath_mono n (leOfHom h).1 (leOfHom h).2⟩⟩⟩

/-- 同じ有限切断を全次数の実単体集合写像として実現する。 -/
def trianglePrismCoordinateSection (n : ℕ) :
    (Δ[1] : SSet.{u}) ⊗ Δ[n] ⟶
      nerve (Path (ULift.up (0 : Fin (n + 3)) : ULift.{u} (Fin (n + 3)))
        (ULift.up (Fin.last (n + 2)))) :=
  (prodStdSimplex.isoNerve 1 n).hom ≫ nerveMap (trianglePrismCoordinateFunctor n)

/-- 二座標を取って零側を切り詰めると、元の区間と全標準単体が厳密に戻る。 -/
lemma trianglePrismCoordinateSection_retract (n : ℕ) :
    trianglePrismCoordinateSection.{u} n ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleLabelPathCoordinates (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.trianglePrismLabel n) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.trianglePrismLabel_zero n)
        (Fin.last (n + 2)) ≫
      (Δ[1] ◁ stdSimplex.map (SimplexCategory.mkHom (trianglePrismRetraction n))) = 𝟙 _ := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨b, k⟩
  apply Prod.ext
  · apply stdSimplex.ext
    intro i
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.trianglePathMiddle (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.trianglePrismLabel n)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.trianglePrismCoordinatePath.{u} n (b i) (k i)) = b i
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.trianglePrismCoordinatePath_middle.{u} n (b i) (k i)
  · apply stdSimplex.ext
    intro i
    change trianglePrismRetraction n
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZero (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleZeroLabel (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.trianglePrismLabel n))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleZeroLabel_zero _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.trianglePrismLabel_zero n))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.trianglePrismCoordinatePath.{u} n (b i) (k i))) = k i
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.trianglePrismCoordinatePath_lastZero.{u}]
    apply Fin.ext
    exact min_eq_left (Nat.le_of_lt_succ (k i).isLt)

/-- 同じ native path の二座標は全射。 -/
instance trianglePrismCoordinates_epi (n : ℕ) :
    Epi (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleLabelPathCoordinates (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.trianglePrismLabel n) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.trianglePrismLabel_zero n)
      (Fin.last (n + 2)) ≫
      (Δ[1] ◁ stdSimplex.map (SimplexCategory.mkHom (trianglePrismRetraction n))) :
      nerve (Path (ULift.up (0 : Fin (n + 3)) : ULift.{u} (Fin (n + 3)))
        (ULift.up (Fin.last (n + 2)))) ⟶ (Δ[1] : SSet.{u}) ⊗ Δ[n]) :=
  epi_of_epi_fac (trianglePrismCoordinateSection_retract n)

/-- 同じ二座標を前合成した全族から、元の区間・標準単体族を厳密に回収する。 -/
lemma trianglePrismCoordinates_precomp_injective (n : ℕ) {H : SSet.{u}}
    (q r : (Δ[1] : SSet.{u}) ⊗ Δ[n] ⟶ H)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleLabelPathCoordinates (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.trianglePrismLabel n) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.trianglePrismLabel_zero n)
        (Fin.last (n + 2)) ≫
        (Δ[1] ◁ stdSimplex.map (SimplexCategory.mkHom (trianglePrismRetraction n))) ≫ q =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleLabelPathCoordinates (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.trianglePrismLabel n) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.trianglePrismLabel_zero n)
        (Fin.last (n + 2)) ≫
        (Δ[1] ◁ stdSimplex.map (SimplexCategory.mkHom (trianglePrismRetraction n))) ≫ r) :
    q = r := by
  exact (cancel_epi (_ ≫ (Δ[1] ◁ stdSimplex.map
    (SimplexCategory.mkHom (trianglePrismRetraction n))))).mp h

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
