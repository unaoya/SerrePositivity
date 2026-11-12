module

public import SerrePositivity.AlgebraicGeometry.OpenCoverCechResolutionRows
public import SerrePositivity.AlgebraicGeometry.OpenCoverCechResolutionZero
public import SerrePositivity.HomologicalAlgebra.Cech.Diagonal

/-!
概要：二つの開被覆の増大 Čech を、B1 に渡す実際の二重図式として作る。
方針：一方の増大 Čech 前層に他方の Čech 構成を適用する。
規約：二つの微分は可換で、符号の変更は既存 B1 の判定に任せる。
使われ方：アフィン被覆の完全性と、一般の細分の比較の列の完全性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory TopologicalSpace Opposite
universe u v
variable {X : Type u} [TopologicalSpace X] {R : Type v} [CommRing R]
variable (P : (Opens X)ᵒᵖ ⥤ ModuleCat.{v} R) {ι κ : Type} [LinearOrder ι] [LinearOrder κ]
variable (U : ι → Opens X) (V : κ → Opens X)

/-- 二つの被覆の実際の増大 Čech の二重図式の項。 -/
abbrev openCoverCechDoubleTerm (i j : ℕ) : Type v :=
  FullCechCochains (openCoverCechDiagram (openCoverCechResolution P V j) U) i

/-- 二重 Čech の水平方向の余境界。 -/
def openCoverCechDoubleHorizontal (i j : ℕ) :
    openCoverCechDoubleTerm P U V i j →+ openCoverCechDoubleTerm P U V (i + 1) j :=
  (fullCechDifferential (openCoverCechDiagram (openCoverCechResolution P V j) U) i).toAddHom

/-- 二重 Čech の垂直方向の余境界。 -/
def openCoverCechDoubleVertical (i j : ℕ) :
    openCoverCechDoubleTerm P U V i j →+ openCoverCechDoubleTerm P U V i (j + 1) :=
  (fullCechCochainsMap
    (openCoverCechCoefficientMap (openCoverCechResolutionDifferential P V j) U) i).toAddHom

/-- 水平方向の微分の二乗は零。 -/
theorem openCoverCechDoubleHorizontal_squared (i j : ℕ)
    (x : openCoverCechDoubleTerm P U V i j) :
    openCoverCechDoubleHorizontal P U V (i + 1) j
      (openCoverCechDoubleHorizontal P U V i j x) = 0 :=
  LinearMap.congr_fun (fullCechAugmentedDifferential_squared
    (openCoverCechDiagram (openCoverCechResolution P V j) U) i) x

/-- 垂直方向の微分の二乗は零。 -/
theorem openCoverCechDoubleVertical_squared (i j : ℕ)
    (x : openCoverCechDoubleTerm P U V i j) :
    openCoverCechDoubleVertical P U V i (j + 1)
      (openCoverCechDoubleVertical P U V i j x) = 0 := by
  funext t
  exact congrArg (fun η : openCoverCechResolution P V j ⟶
      openCoverCechResolution P V (j + 2) ↦ (η.app (op (cechOpenIntersection U (cechTupleSupport t)))).hom (x t))
    (openCoverCechResolutionDifferential_squared P V j)

/-- 二つの方向の Čech 微分は可換。 -/
theorem openCoverCechDouble_commute (i j : ℕ) (x : openCoverCechDoubleTerm P U V i j) :
    openCoverCechDoubleHorizontal P U V i (j + 1)
        (openCoverCechDoubleVertical P U V i j x) =
      openCoverCechDoubleVertical P U V (i + 1) j
        (openCoverCechDoubleHorizontal P U V i j x) :=
  (LinearMap.congr_fun (fullCechCochainsMap_comp_differential
    (openCoverCechCoefficientMap (openCoverCechResolutionDifferential P V j) U) i) x).symm

/-- 細分の包含から、正次数の行の完全性を得る。 -/
theorem openCoverCechDouble_rowExact (ρ : κ → ι) (hρ : ∀ i, V i ≤ U (ρ i))
    (j : ℕ) (hj : 0 < j) :
    SerrePositivity.Cech.RowExact (openCoverCechDoubleTerm P U V)
      (openCoverCechDoubleHorizontal P U V) j := by
  constructor
  · intro x hx
    apply openCoverCechResolutionRow_zero_injective P U V ρ hρ j hj
    change fullCechDifferential
      (openCoverCechDiagram (openCoverCechResolution P V j) U) 0 x = 0 at hx
    simpa only [map_zero] using hx
  · intro i x hx
    exact (openCoverCechResolutionRow_exact P U V ρ hρ j hj i x).mp hx

/-- 各水平交叉上の増大 Čech が完全なら、その直積である列も完全。 -/
theorem openCoverCechDouble_colExact (i : ℕ)
    (hzero : ∀ t : Fin i → ι, Function.Injective
      (fullCechDifferential (openCoverCechDiagram (openCoverIntersectionPresheaf P
        (cechOpenIntersection U (cechTupleSupport t))) V) 0))
    (hexact : ∀ (t : Fin i → ι) (j : ℕ), Function.Exact
      (fullCechDifferential (openCoverCechDiagram (openCoverIntersectionPresheaf P
        (cechOpenIntersection U (cechTupleSupport t))) V) j)
      (fullCechDifferential (openCoverCechDiagram (openCoverIntersectionPresheaf P
        (cechOpenIntersection U (cechTupleSupport t))) V) (j + 1))) :
    SerrePositivity.Cech.ColExact (openCoverCechDoubleTerm P U V)
      (openCoverCechDoubleVertical P U V) i := by
  constructor
  · intro x hx
    funext t
    apply hzero t
    change fullCechDifferential (openCoverCechDiagram (openCoverIntersectionPresheaf P
      (cechOpenIntersection U (cechTupleSupport t))) V) 0 (x t) = _
    have hxt : fullCechDifferential (openCoverCechDiagram (openCoverIntersectionPresheaf P
      (cechOpenIntersection U (cechTupleSupport t))) V) 0 (x t) = 0 := congrFun hx t
    simpa only [Pi.zero_apply, map_zero] using hxt
  · intro j x hx
    have hs (t : Fin i → ι) : ∃ y,
        fullCechDifferential (openCoverCechDiagram (openCoverIntersectionPresheaf P
          (cechOpenIntersection U (cechTupleSupport t))) V) j y = x t := by
      apply (hexact t j _).mp
      exact congrFun hx t
    choose y hy using hs
    exact ⟨y, funext hy⟩

/-- 二重 Čech に既存 B1 の零番の行・列の比較を適用する。 -/
theorem openCoverCechDouble_exact_zero_iff
    (hr : ∀ j, 0 < j → SerrePositivity.Cech.RowExact (openCoverCechDoubleTerm P U V)
      (openCoverCechDoubleHorizontal P U V) j)
    (hc : ∀ i, 0 < i → SerrePositivity.Cech.ColExact (openCoverCechDoubleTerm P U V)
      (openCoverCechDoubleVertical P U V) i) :
    SerrePositivity.Cech.RowExact (openCoverCechDoubleTerm P U V)
        (openCoverCechDoubleHorizontal P U V) 0 ↔
      SerrePositivity.Cech.ColExact (openCoverCechDoubleTerm P U V)
        (openCoverCechDoubleVertical P U V) 0 :=
  SerrePositivity.Cech.exact_zero_row_iff_zero_col_of_commute
    (openCoverCechDoubleTerm P U V) (openCoverCechDoubleHorizontal P U V)
    (openCoverCechDoubleVertical P U V)
    (openCoverCechDoubleHorizontal_squared P U V)
    (openCoverCechDoubleVertical_squared P U V)
    (openCoverCechDouble_commute P U V) hr hc

end SerrePositivity.AlgebraicGeometry
