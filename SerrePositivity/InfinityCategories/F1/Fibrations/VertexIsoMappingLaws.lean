module

public import SerrePositivity.InfinityCategories.Core.FunctorHomotopy
public import SerrePositivity.InfinityCategories.F1.Fibrations.VertexIsoMapCoherence

/-!
概要：指定された頂点同型の像の合成と、定値写像による恒等性。
方針：ホモトピー圏の関手性と、零単体への定値射による分解で計算する。
規約：始域の充填性を仮定せず、指定同型の像自体を比較する。
使われ方：比較 Hom の fiber 内で作った同型の射影の coherence。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 同じ頂点同型の二回の像は、合成した元の射による像。 -/
lemma VertexIso.map_comp {X Y Z : SSet.{u}} {x y : X _⦋0⦌}
    (e : VertexIso x y) (f : X ⟶ Y) (g : Y ⟶ Z) :
    VertexIso.map (VertexIso.map e f) g = VertexIso.map e (f ≫ g) :=
  vertexIso_map_comp e f g

/-- 定値写像による指定頂点同型の像は、同じ頂点の恒等同型。 -/
lemma VertexIso.map_const {X Y : SSet.{u}}
    {x y : X _⦋0⦌} (e : VertexIso x y) (b : Y _⦋0⦌) :
    VertexIso.map e (SSet.const b : X ⟶ Y) =
      Iso.refl (SSet.HomotopyCategory.mk ((SSet.const b : X ⟶ Y).app _ x)) := by
  let t : X ⟶ (Δ[0] : SSet.{u}) := SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1))
  have ht : VertexIso.map e t = Iso.refl _ := by
    apply Iso.ext
    exact Subsingleton.elim _ _
  have hv := vertexIso_map_comp e t (SSet.const b)
  rw [ht] at hv
  simp only [VertexIso.map, Functor.mapIso_refl] at hv
  convert hv.symm using 1 <;> rfl

/-- 同じ射の表示を等式で変更した像は、指定された端点の等号で移送される。 -/
lemma VertexIso.map_congr {X Y : SSet.{u}} {x y : X _⦋0⦌}
    (e : VertexIso x y) {f g : X ⟶ Y} (h : f = g) :
    VertexIso.map e f =
      eqToIso (congrArg SSet.HomotopyCategory.mk
        (congrArg (fun t : X ⟶ Y ↦ t.app (Opposite.op ⦋0⦌) x) h)) ≪≫
      VertexIso.map e g ≪≫
      (eqToIso (congrArg SSet.HomotopyCategory.mk
        (congrArg (fun t : X ⟶ Y ↦ t.app (Opposite.op ⦋0⦌) y) h))).symm := by
  subst g
  simp

end SerrePositivity.InfinityCategories
