module
public import SerrePositivity.InfinityCategories.Derived.Gluing.UnitTriangleRelativeLoopComparison
public import SerrePositivity.InfinityCategories.Derived.Gluing.RelativeHomotopyEdgeClass
/-! # 相対単位三角形比較が与える対角閉路の零性

概要：退化単位三角形への三辺固定比較から、元対角閉路の関手圏の類が恒等射となることを得る。
方針：四辺固定の実比較を区間写像空間へ戻し、両端固定二変形の類を比較する。
規約：相対比較だけを明示入力とし、元閉路と全時間を保持する。
使われ方：選択済み四面体の左単位面を、六角形関係の中で消去する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
variable {K Z : SSet.{u}} {x y : Z _⦋0⦌}
  (b : K ⟶ intervalMappingSpace x y) (l : SSet.Homotopy b b)
  (A : (Δ[2] : SSet.{u}) ⊗ K ⟶ Z)
  (H : SSet.Homotopy A ((stdSimplex.σ (0 : Fin 2) ▷ K) ≫ intervalMappingUncurry b))
  (ha : dgGluingInitialUnitConeFamily K ≫ A = intervalMappingUncurry l.h)
  (hfaces : ∀ i : Fin 3, ((stdSimplex.δ i ▷ K) ▷ (Δ[1] : SSet.{u})) ≫ H.h =
    fst (Δ[1] ⊗ K) Δ[1] ≫ (stdSimplex.δ i ▷ K) ≫
      (stdSimplex.σ (0 : Fin 2) ▷ K) ≫ intervalMappingUncurry b)

def dgGluingUnitTriangleLoopRelativeHomotopy :
    SSet.Homotopy l.h (functorHomotopyRefl b).h :=
  dgGluingIntervalUncurryHomotopyInverse
    (dgGluingUnitTriangleLoopUncurriedHomotopy b l A H ha)
    (dgGluingUnitTriangleLoopUncurriedHomotopy_source b l A H ha hfaces)
    (dgGluingUnitTriangleLoopUncurriedHomotopy_target b l A H ha hfaces)

include hfaces ha in
lemma dgGluingUnitTriangleLoop_homMk_refl :
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy l) =
      SSet.Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy (functorHomotopyRefl b)) := by
  let T := dgGluingUnitTriangleLoopUncurriedHomotopy b l A H ha
  let hx := dgGluingUnitTriangleLoopUncurriedHomotopy_source b l A H ha hfaces
  let hy := dgGluingUnitTriangleLoopUncurriedHomotopy_target b l A H ha hfaces
  apply dgGluingRelativeHomotopy_homMk_eq l (functorHomotopyRefl b)
    (dgGluingUnitTriangleLoopRelativeHomotopy b l A H ha hfaces)
  · have he := dgGluingIntervalUncurryHomotopyInverse_fixed T hx hy (ι₀ : K ⟶ _)
      (dgGluingUnitTriangleLoopUncurriedHomotopy_zero_fixed b l A H ha hfaces)
    simpa only [dgGluingUnitTriangleLoopRelativeHomotopy, T, hx, hy,
      Category.assoc, SSet.Homotopy.h₀] using he
  · have he := dgGluingIntervalUncurryHomotopyInverse_fixed T hx hy (ι₁ : K ⟶ _)
      (dgGluingUnitTriangleLoopUncurriedHomotopy_one_fixed b l A H ha hfaces)
    simpa only [dgGluingUnitTriangleLoopRelativeHomotopy, T, hx, hy,
      Category.assoc, SSet.Homotopy.h₁] using he

include hfaces ha in
lemma dgGluingUnitTriangleLoop_homMk_id :
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy l) = 𝟙 _ := by
  rw [dgGluingUnitTriangleLoop_homMk_refl b l A H ha hfaces,
    functorHomotopyRefl_hom]
  rfl
end SerrePositivity.InfinityCategories
