module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakHomotopy
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex

/-!
概要：任意の単体集合の連結成分へのラベルを、元の全単体上の定値対象への射にする。
方針：同じ単体の各頂点の連結成分の一致を使い、最初の頂点で評価する。
規約：元の全空間の Kan 性は不要。元の頂点で同じラベルを厳密に回収する。
使われ方：元の Kan 置換単位の π₀ 全射性による、余極限の点の回収。

対応節は Kerodon 9.2（Tag 0639）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects

/-- 同じ元の単体の任意の頂点は、最初の頂点と同じ連結成分に属する。 -/
lemma simplexVertex_component {X : SSet.{u}} {n : ℕ} (s : X _⦋n⦌)
    (i : Fin (n + 1)) :
    SSet.π₀.mk (X.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0).op s) =
      SSet.π₀.mk (X.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i).op s) := by
  let e : SSet.Edge (X := (Δ[n] : SSet.{u}))
      (stdSimplex.obj₀Equiv.symm 0) (stdSimplex.obj₀Equiv.symm i) :=
    ⟨stdSimplex.edge n 0 i (Fin.zero_le _), by
      apply SSet.stdSimplex.ext
      intro j
      fin_cases j
      rfl, by
      apply SSet.stdSimplex.ext
      intro j
      fin_cases j
      rfl⟩
  exact SSet.π₀.sound (e.map (SSet.yonedaEquiv.symm s))

/-- 元の単体の最初の頂点の成分は、全ての面・退化に対して自然。 -/
lemma simplexFirstVertex_component_naturality {X : SSet.{u}}
    {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m) (s : X.obj n) :
    SSet.π₀.mk (X.map (SimplexCategory.const ⦋0⦌ m.unop 0).op (X.map α s)) =
      SSet.π₀.mk (X.map (SimplexCategory.const ⦋0⦌ n.unop 0).op s) := by
  rw [← CategoryTheory.Functor.map_comp_apply]
  change SSet.π₀.mk (X.map ((SimplexCategory.const ⦋0⦌ m.unop 0) ≫ α.unop).op s) = _
  have h : SimplexCategory.const ⦋0⦌ m.unop 0 ≫ α.unop =
      SimplexCategory.const ⦋0⦌ n.unop (α.unop.toOrderHom 0) := by
    ext j
    rfl
  rw [h]
  exact (simplexVertex_component s (α.unop.toOrderHom 0)).symm

/-- 元の連結成分への任意のラベルを、全単体上の定値対象への実際の射として表示。 -/
def componentLabelMap (X : SSet.{u}) {T : Type u} (a : SSet.π₀ X → T) :
    X ⟶ (CategoryTheory.Functor.const SimplexCategoryᵒᵖ).obj T where
  app n := ↾fun s ↦ a (SSet.π₀.mk (X.map (SimplexCategory.const ⦋0⦌ n.unop 0).op s))
  naturality n m α := by
    apply ConcreteCategory.hom_ext
    intro s
    exact congrArg a (simplexFirstVertex_component_naturality α s)

/-- 同じ元の頂点でのラベルを、厳密に回収する。 -/
lemma componentLabelMap_zero (X : SSet.{u}) {T : Type u} (a : SSet.π₀ X → T)
    (x : X _⦋0⦌) : (componentLabelMap X a).app (Opposite.op ⦋0⦌) x = a (SSet.π₀.mk x) := by
  change a (SSet.π₀.mk (X.map (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0).op x)) = _
  have h : SimplexCategory.const ⦋0⦌ ⦋0⦌ 0 = 𝟙 _ := Subsingleton.elim _ _
  rw [h, op_id, CategoryTheory.Functor.map_id_apply]

/-- 元のラベルの全写像は、元の射への前合成と厳密に可換。 -/
lemma componentLabelMap_pre {X Y : SSet.{u}} (f : X ⟶ Y) {T : Type u}
    (a : SSet.π₀ Y → T) :
    f ≫ componentLabelMap Y a = componentLabelMap X (a ∘ SSet.mapπ₀ f) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  change a (SSet.π₀.mk (Y.map (SimplexCategory.const ⦋0⦌ n.unop 0).op (f.app n s))) =
    a (SSet.π₀.mk (f.app _ (X.map (SimplexCategory.const ⦋0⦌ n.unop 0).op s)))
  exact congrArg (fun x ↦ a (SSet.π₀.mk x))
    (ConcreteCategory.congr_hom (f.naturality (SimplexCategory.const ⦋0⦌ n.unop 0).op) s).symm

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects
