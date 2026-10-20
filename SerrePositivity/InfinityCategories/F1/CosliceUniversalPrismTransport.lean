module

public import SerrePositivity.InfinityCategories.F1.CosliceUniversalPrismComparison
public import SerrePositivity.InfinityCategories.F1.MappingSpaceIntervalComparison
public import SerrePositivity.InfinityCategories.F1.DiagonalFiberTransport

/-!
概要：coslice 上の実際の大域射の fiber 作用を、同じ標準区間族の輸送へ移す。
方針：始点固定の普遍 prism を fiber へ制限し、その終点を大域比較の一意性で戻す。
規約：元の coslice fiber の全単体を同時に扱い、既存の標準区間比較を使う。
使われ方：表現可能 Hom の大域比較の fiber 同値性を、恒等射の輸送で検証する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 普遍区間の fiber への制限は、既存の coslice の標準区間比較そのもの。 -/
lemma cosliceUniversalPrism_fiber {B : SSet.{u}} (b r : B _⦋0⦌) :
    (Δ[1] ◁ vertexFiberι (sliceUnderProjection (SSet.yonedaEquiv.symm b)) r) ≫
      cosliceUniversalPrism b = intervalMappingUncurry
        (cosliceFiberToIntervalMappingSpace b r) := by
  rw [cosliceUniversalPrism_precomp]
  simpa only [Category.id_comp, cosliceFiberUncurry] using
    (cosliceFiberToIntervalMappingSpace_uncurry
      (𝟙 (vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm b)) r))).symm

/-- 持ち上げの実際の終点の fiber 作用は、同じ coslice 区間族の恒等点からの輸送。 -/
def cosliceUniversalPrismLiftEndpoint_transportIso {E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (b : B _⦋0⦌) (d : E _⦋0⦌)
    (hd : p.app (Opposite.op ⦋0⦌) d = b) (r : B _⦋0⦌) :
    FunctorIso
      (vertexFiberMap _ p (cosliceUniversalPrismLiftEndpoint p b d hd)
        (cosliceUniversalPrismLiftEndpoint_projection p b d hd) r)
      (diagonalFiberTransport p
        (SSet.const (⟨d, by rw [PinchedHom.constant_zero]; exact hd⟩ :
          (vertexFiber p b) _⦋0⦌)) (cosliceFiberToIntervalMappingSpace b r)) := by
  let P := vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm b)) r
  let i := vertexFiberι (sliceUnderProjection (SSet.yonedaEquiv.symm b)) r
  let γ := intervalMappingUncurry (cosliceFiberToIntervalMappingSpace b r)
  let W := (Δ[1] ◁ i) ≫ cosliceUniversalPrismLift p b d hd
  let x : P ⟶ vertexFiber p b :=
    SSet.const ⟨d, by rw [PinchedHom.constant_zero]; exact hd⟩
  let g := vertexFiberMap _ p (cosliceUniversalPrismLiftEndpoint p b d hd)
    (cosliceUniversalPrismLiftEndpoint_projection p b d hd) r
  have h₀ := intervalMappingUncurry_zero (cosliceFiberToIntervalMappingSpace b r)
  have h₁ := intervalMappingUncurry_one (cosliceFiberToIntervalMappingSpace b r)
  have W₀ : prismEndpoint 0 P ≫ W = x ≫ vertexFiberι p b := by
    dsimp only [W]
    rw [← Category.assoc, prismEndpoint_naturality, Category.assoc,
      cosliceUniversalPrismLift_zero, SSet.comp_const]
    rfl
  have W₁ : prismEndpoint 1 P ≫ W = g ≫ vertexFiberι p r := by
    dsimp only [W]
    rw [← Category.assoc, prismEndpoint_naturality, Category.assoc]
    exact (vertexFiberMap_ι _ p (cosliceUniversalPrismLiftEndpoint p b d hd)
      (cosliceUniversalPrismLiftEndpoint_projection p b d hd) r).symm
  have Wp : W ≫ p = γ := by
    rw [Category.assoc, cosliceUniversalPrismLift_projection]
    exact cosliceUniversalPrism_fiber b r
  have e := leftFibrationPrism_diagonalTransportIso p x g γ h₀ h₁ W W₀ W₁ Wp
  have hc : intervalMappingCurryOfEndpoints γ h₀ h₁ =
      cosliceFiberToIntervalMappingSpace b r := by
    apply intervalMappingUncurry_injective b r
    exact intervalMappingUncurry_curryOfEndpoints γ h₀ h₁
  rw [hc] at e
  exact e

/-- 任意の大域射の実際の fiber 作用は、同じ指定始点からの標準 coslice 輸送と同型。 -/
def leftFibrationCosliceMap_transportIso {E B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [LeftFibration p] (b : B _⦋0⦌) (d : E _⦋0⦌)
    (hd : p.app (Opposite.op ⦋0⦌) d = b)
    (f : sliceUnder (SSet.yonedaEquiv.symm b) ⟶ E)
    (hf : f ≫ p = sliceUnderProjection (SSet.yonedaEquiv.symm b))
    (h : f.app (Opposite.op ⦋0⦌) (cosliceIdentityCone b) = d) (r : B _⦋0⦌) :
    FunctorIso (vertexFiberMap _ p f hf r)
      (diagonalFiberTransport p
        (SSet.const (⟨d, by rw [PinchedHom.constant_zero]; exact hd⟩ :
          (vertexFiber p b) _⦋0⦌)) (cosliceFiberToIntervalMappingSpace b r)) :=
  (cosliceUniversalPrismLiftEndpoint_fiberIso p b d hd f hf h r).symm ≪≫
    cosliceUniversalPrismLiftEndpoint_transportIso p b d hd r

end SerrePositivity.InfinityCategories
