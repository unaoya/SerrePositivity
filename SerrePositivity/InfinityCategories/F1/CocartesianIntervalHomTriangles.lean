module

public import SerrePositivity.InfinityCategories.F1.CocartesianHomFixedComponentPresentation
public import SerrePositivity.InfinityCategories.F1.ParameterizedSquare
public import SerrePositivity.InfinityCategories.F1.LocalKanDiagramStrictification

/-!
概要：一次元の実際の固定成分 fiber の族を、同じ正方形の二つの三角形に分ける。
方針：底の標準単体の同型で元の prism を移し、対角の一致と全パラメーターの一意性を使う。
規約：元の図式・成分と正方形そのものを保持する。
使われ方：一次元の固定成分比較を、合成三角形の実際の比較へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable (F G : CocartesianTransportDiagramCategory (ULift.{u} (Fin 2)))
local notation "c" => (ULift.up (1 : Fin 2))
variable (v : (intervalMappingSpace (coherentNerveVertex (cocartesianTransportDiagramValue F c))
  (coherentNerveVertex (cocartesianTransportDiagramValue G c))) _⦋0⦌)
local notation "E" => (vertexFiber (cocartesianHomIntervalEvaluation F G c) v)

/-- 元の一次元の固定成分 fiber の族を、標準正方形上の同じ図式にする。 -/
def cocartesianIntervalHomSquare {T : SSet.{u + 1}} (f : T ⟶ E) :
    ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1]) ⊗ T ⟶ CatInfinity.{u} :=
  ((Δ[1] ◁ (localKanDiagramBaseIso.{u} 1).hom) ▷ T) ≫
    cocartesianHomFixedComponentPrism F G c v f

/-- 同じ正方形の i 番目の実際の三角形を、全パラメーターで制限する。 -/
def cocartesianIntervalHomTriangle {T : SSet.{u + 1}} (i : Fin 2) (f : T ⟶ E) :
    (Δ[2] : SSet.{u + 1}) ⊗ T ⟶ CatInfinity.{u} :=
  (squareTriangle i ▷ T) ≫ cocartesianIntervalHomSquare F G v f

/-- 二つの実際の三角形は、同じ正方形の元の対角を全パラメーターで共有する。 -/
lemma cocartesianIntervalHomTriangle_diagonal {T : SSet.{u + 1}} (i : Fin 2) (f : T ⟶ E) :
    (stdSimplex.δ (1 : Fin 3) ▷ T) ≫ cocartesianIntervalHomTriangle F G v i f =
      (squareDiagonal ▷ T) ≫ cocartesianIntervalHomSquare F G v f := by
  unfold cocartesianIntervalHomTriangle
  rw [← Category.assoc, ← comp_whiskerRight, squareTriangle_diagonal]

/-- 元の実際の固定成分 fiber の族は、同じ二つの三角形で一意に決まる。 -/
lemma cocartesianIntervalHomTriangle_hom_ext {T : SSet.{u + 1}} (f g : T ⟶ E)
    (h₀ : cocartesianIntervalHomTriangle F G v 0 f = cocartesianIntervalHomTriangle F G v 0 g)
    (h₁ : cocartesianIntervalHomTriangle F G v 1 f = cocartesianIntervalHomTriangle F G v 1 g) :
    f = g := by
  apply cocartesianHomFixedComponentPrism_injective F G c v
  have h := parameterizedSquare_hom_ext (cocartesianIntervalHomSquare F G v f)
    (cocartesianIntervalHomSquare F G v g) h₀ h₁
  unfold cocartesianIntervalHomSquare at h
  exact (cancel_epi _).mp h

end SerrePositivity.InfinityCategories
