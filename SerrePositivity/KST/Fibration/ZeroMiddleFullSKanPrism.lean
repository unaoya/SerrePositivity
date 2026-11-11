module
public import SerrePositivity.KST.Fibration.ZeroMiddleFullSKanHorn
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.TriangleMiddlePrism
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy

/-!
概要：元の零中間二胞体を端面に保持する、全 S• 中間対象への実三角柱。
方針：同じ実内角を充填し、公開三角柱写像で全パラメーターへ戻す。
規約：元の全二胞体は終端で厳密回収し、共有対角は全時刻固定する。
使われ方：K-6 c4。選択した始端二胞体を指定四角形比較へ貼り合わせる実入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} _⦋2⦌) (hZ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (s.obj ⟨ULift.up 1⟩))

/-- 元の二胞体を面 1 とする内角の、指定した一つの実充填。 -/
def zeroMiddleFullSKanTetrahedron : (Δ[3] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  Classical.choose (Quasicategory.hornFilling (by decide) (by decide)
    (zeroMiddleFullSKanHorn s hZ))

/-- 充填は、元の二胞体と同じ二つの厳密合成二胞体を含む全内角を保持する。 -/
theorem zeroMiddleFullSKanTetrahedron_horn :
    zeroMiddleFullSKanHorn s hZ = (horn 3 (2 : Fin 4)).ι ≫
      zeroMiddleFullSKanTetrahedron s hZ :=
  Classical.choose_spec (Quasicategory.hornFilling (by decide) (by decide)
    (zeroMiddleFullSKanHorn s hZ))

/-- 元の native 二胞体は、選択した充填の面 1 から全二単体で厳密に戻る。 -/
theorem zeroMiddleFullSKanTetrahedron_original :
    stdSimplex.δ (1 : Fin 4) ≫ zeroMiddleFullSKanTetrahedron s hZ =
      SSet.yonedaEquiv.symm ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap stableCoreSingleKanEnrichedFunctor).app
        (Opposite.op ⦋2⦌) s) := by
  calc
    _ = horn₃₂.ι₁ ≫ ((horn 3 (2 : Fin 4)).ι ≫
        zeroMiddleFullSKanTetrahedron s hZ) := by rw [← Category.assoc, horn.ι_ι]
    _ = horn₃₂.ι₁ ≫ zeroMiddleFullSKanHorn s hZ := by
      rw [← zeroMiddleFullSKanTetrahedron_horn]
    _ = _ := zeroMiddleFullSKanHorn_original s hZ

/-- 全 S• 中間頂点を持つ始端は、同じ実充填の面 2 として保持する。 -/
def zeroMiddleFullSKanTransportedTriangle : (Δ[2] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  stdSimplex.δ (2 : Fin 4) ≫ zeroMiddleFullSKanTetrahedron s hZ

/-- 元の全二胞体を終端に厳密保持する、同じ全 S• 中間対象の実三角柱。 -/
def zeroMiddleFullSKanPrism : SSet.Homotopy (zeroMiddleFullSKanTransportedTriangle s hZ)
    (SSet.yonedaEquiv.symm ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap stableCoreSingleKanEnrichedFunctor).app
      (Opposite.op ⦋2⦌) s)) where
  h := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.triangleMiddlePrism ≫ zeroMiddleFullSKanTetrahedron s hZ
  h₀ := by rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.triangleMiddlePrism_zero]; rfl
  h₁ := by rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.triangleMiddlePrism_one,
    zeroMiddleFullSKanTetrahedron_original]; rfl
  rel := by ext n t; exact False.elim t.1.2

/-- 同じ実三角柱は、元の長辺の全単体を全時刻で固定する。 -/
theorem zeroMiddleFullSKanPrism_diagonal :
    (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫ (zeroMiddleFullSKanPrism s hZ).h =
      CartesianMonoidalCategory.fst (Δ[1] : SSet.{u + 1}) Δ[1] ≫
        stdSimplex.δ (1 : Fin 3) ≫ zeroMiddleFullSKanTransportedTriangle s hZ := by
  change _ ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.triangleMiddlePrism ≫ _) = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.triangleMiddlePrism_diagonal]
  simp only [zeroMiddleFullSKanTransportedTriangle, Category.assoc]

end SerrePositivity.KST.Fibration
