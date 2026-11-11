module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalMappingFaceEndpoints
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceIntervalComparison

/-!
概要：二つの頂点の面を固定した区間族を、同じ両端固定 Hom 空間へ戻す。
方針：標準零単体の点を補って面の条件を端点の条件へ移す。
規約：全パラメーターの元の族を厳密に回収する。
使われ方：合成三角形全体の対角を Hom 空間への射として束ねる。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 元の両頂点の面を固定した同じ区間族から、固定端点の Hom 空間への射を得る。 -/
def intervalMappingCurryOfVertexFaces {T X : SSet.{u}} {x y : X _⦋0⦌}
    (H : (Δ[1] : SSet.{u}) ⊗ T ⟶ X)
    (h₀ : (stdSimplex.δ (1 : Fin 2) ▷ T) ≫ H =
      fst (Δ[0] : SSet.{u}) T ≫ SSet.yonedaEquiv.symm x)
    (h₁ : (stdSimplex.δ (0 : Fin 2) ▷ T) ≫ H =
      fst (Δ[0] : SSet.{u}) T ≫ SSet.yonedaEquiv.symm y) : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y := by
  let s : T ⟶ (Δ[0] : SSet.{u}) ⊗ T :=
    lift (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) (𝟙 T)
  refine _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingCurryOfEndpoints H ?_ ?_
  · have h := congrArg (fun q ↦ s ≫ q) h₀
    exact h
  · have h := congrArg (fun q ↦ s ≫ q) h₁
    exact h

/-- 展開すると、二つの頂点の面を固定した元の区間族そのもの。 -/
lemma intervalMappingCurryOfVertexFaces_uncurry {T X : SSet.{u}} {x y : X _⦋0⦌}
    (H : (Δ[1] : SSet.{u}) ⊗ T ⟶ X)
    (h₀ : (stdSimplex.δ (1 : Fin 2) ▷ T) ≫ H =
      fst (Δ[0] : SSet.{u}) T ≫ SSet.yonedaEquiv.symm x)
    (h₁ : (stdSimplex.δ (0 : Fin 2) ▷ T) ≫ H =
      fst (Δ[0] : SSet.{u}) T ≫ SSet.yonedaEquiv.symm y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (intervalMappingCurryOfVertexFaces H h₀ h₁) = H := by
  unfold intervalMappingCurryOfVertexFaces
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_curryOfEndpoints]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
