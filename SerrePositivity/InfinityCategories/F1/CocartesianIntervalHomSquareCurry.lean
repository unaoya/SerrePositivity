module

public import SerrePositivity.InfinityCategories.F1.CocartesianIntervalHomSquareFaces
public import SerrePositivity.InfinityCategories.F1.LocalIntervalSquareReindex

/-!
概要：同じ三辺を固定した標準正方形を、元の固定成分 Hom fiber の族へ戻す。
方針：底の逆同型で元の prism に戻し、既存の同じ固定成分の curry を使う。
規約：標準化した正方形全体を、全パラメーターで厳密に回収する。
使われ方：第二三角形の外ホーン延長から、元の pullback の持ち上げを構成する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable (F G : CocartesianTransportDiagramCategory (ULift.{u} (Fin 2)))
local notation "c" => (ULift.up (1 : Fin 2))
variable (v : (intervalMappingSpace (coherentNerveVertex (cocartesianTransportDiagramValue F c))
  (coherentNerveVertex (cocartesianTransportDiagramValue G c))) _⦋0⦌)
local notation "E" => (vertexFiber (cocartesianHomIntervalEvaluation F G c) v)
local notation "D₀" => (qCatDiagramCoherentNerve (cocartesianTransportDiagramValueFunctor F))
local notation "D₁" => (qCatDiagramCoherentNerve (cocartesianTransportDiagramValueFunctor G))

/-- 元の三辺を固定した標準正方形を、実際の固定成分 Hom fiber の同じ族へ戻す。 -/
def cocartesianIntervalHomSquareCurry {T : SSet.{u + 1}}
    (H : ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1]) ⊗ T ⟶ CatInfinity.{u})
    (h₀ : (prismEndpoint 0 Δ[1] ▷ T) ≫ H =
      fst (Δ[1] : SSet.{u + 1}) T ≫ (localKanDiagramBaseIso 1).hom ≫ D₀)
    (h₁ : (prismEndpoint 1 Δ[1] ▷ T) ≫ H =
      fst (Δ[1] : SSet.{u + 1}) T ≫ (localKanDiagramBaseIso 1).hom ≫ D₁)
    (hc : (lift (𝟙 (Δ[1] : SSet.{u + 1}))
      (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) ▷ T) ≫ H =
        intervalMappingUncurry (SSet.const v : T ⟶ _)) : T ⟶ E :=
  cocartesianHomFixedComponentCurry F G c v (localIntervalSquareReindex H)
    (localIntervalSquareReindex_endpoint H 0 D₀ h₀)
    (localIntervalSquareReindex_endpoint H 1 D₁ h₁)
    (by rw [localIntervalSquareReindex_at]; exact hc)

/-- 同じ標準正方形を元の fiber の族に戻して標準化すると、元の正方形を厳密に回収する。 -/
lemma cocartesianIntervalHomSquare_curry {T : SSet.{u + 1}}
    (H : ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1]) ⊗ T ⟶ CatInfinity.{u})
    (h₀ : (prismEndpoint 0 Δ[1] ▷ T) ≫ H =
      fst (Δ[1] : SSet.{u + 1}) T ≫ (localKanDiagramBaseIso 1).hom ≫ D₀)
    (h₁ : (prismEndpoint 1 Δ[1] ▷ T) ≫ H =
      fst (Δ[1] : SSet.{u + 1}) T ≫ (localKanDiagramBaseIso 1).hom ≫ D₁)
    (hc : (lift (𝟙 (Δ[1] : SSet.{u + 1}))
      (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) ▷ T) ≫ H =
        intervalMappingUncurry (SSet.const v : T ⟶ _)) :
    cocartesianIntervalHomSquare F G v
      (cocartesianIntervalHomSquareCurry F G v H h₀ h₁ hc) = H := by
  unfold cocartesianIntervalHomSquare cocartesianIntervalHomSquareCurry
  rw [cocartesianHomFixedComponentPrism_curry, localIntervalSquareReindex_forward]

end SerrePositivity.InfinityCategories
