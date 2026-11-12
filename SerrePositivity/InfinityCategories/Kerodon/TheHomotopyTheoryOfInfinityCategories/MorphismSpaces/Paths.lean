module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Edges

/-! # 右 pinched Hom の道と右辺ホモトピー

概要：写像空間の辺は、始点側が恒等辺である元の二単体に一致する。
方針：最終点固定延長を低次の面写像に同定し、同じ二単体を両方向に読む。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：写像空間の π₀ と H⁰ の射の比較。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

open CategoryTheory Opposite
open scoped _root_.Simplicial

variable {X : SSet.{u}} {x y : X _⦋0⦌}

/-- 概要：二頂点への零番目の面の最終点固定延長は、三頂点への零番目の面。
方針：二つの頂点で評価する。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：道の終点の元の辺への同定。 -/
lemma extend_δ_zero : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend (SimplexCategory.δ (0 : Fin 2)) = SimplexCategory.δ (0 : Fin 3) := by
  ext i
  fin_cases i <;> rfl

/-- 概要：二頂点への一番目の面の最終点固定延長は、三頂点への一番目の面。
方針：二つの頂点で評価する。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：道の始点の元の辺への同定。 -/
lemma extend_δ_one : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend (SimplexCategory.δ (1 : Fin 2)) = SimplexCategory.δ (1 : Fin 3) := by
  ext i
  fin_cases i <;> rfl

/-- 概要：定値一単体は頂点の零番目の退化。
方針：零単体への二つの射が等しいことを使う。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：先頭面を恒等辺として読む。 -/
lemma constant_one (x : X _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1 = X.σ 0 x := by
  have h : SimplexCategory.const ⦋1⦌ ⦋0⦌ 0 = SimplexCategory.σ 0 := Subsingleton.elim _ _
  exact congrArg (fun α => X.map α.op x) h

/-- 概要：三頂点の最終頂点は零番目の面を二度選んで得られる。
方針：零単体の唯一の頂点で評価する。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：三角形の終端固定条件。 -/
lemma lastVertex_one :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.lastVertex 1 = SimplexCategory.δ (0 : Fin 2) ≫ SimplexCategory.δ (0 : Fin 3) := by
  ext i
  fin_cases i
  rfl

/-- 概要：右 pinched Hom の道を、始点側が恒等辺である合成三角形に読む。
方針：元の二単体を保ち、二つの道の面と先頭面条件を三つの辺の条件へ直す。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：π₀ の関係から元の右辺ホモトピーを得る。 -/
def pathCompStruct {s t : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y) _⦋0⦌} (e : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y).Edge s t) :
    SSet.Edge.CompStruct (SSet.Edge.id x) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.vertexEquiv x y t) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.vertexEquiv x y s) :=
  SSet.Edge.CompStruct.mk e.edge.val
    (by simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.front_eq_δ, show Fin.last (1 + 1) = (2 : Fin 3) from by decide,
          constant_one, SSet.Edge.id_edge, SimplicialObject.δ] using e.edge.source)
    (by
      have h := congrArg (fun a : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex x y 0 => a.val) e.tgt_eq
      change X.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend (SimplexCategory.δ (0 : Fin 2))).op e.edge.val = t.val at h
      simpa only [extend_δ_zero, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.vertexEquiv_edge, SimplicialObject.δ] using h)
    (by
      have h := congrArg (fun a : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex x y 0 => a.val) e.src_eq
      change X.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend (SimplexCategory.δ (1 : Fin 2))).op e.edge.val = s.val at h
      simpa only [extend_δ_one, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.vertexEquiv_edge, SimplicialObject.δ] using h)

/-- 概要：始点側が恒等辺である三角形から右 pinched Hom の道を作る。
方針：同じ二単体に先頭面と終端条件を添え、残る二面を道の両端とする。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：境界関係から写像空間の道を作る。 -/
def pathOfCompStruct {s t : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y) _⦋0⦌}
    (h : SSet.Edge.CompStruct (SSet.Edge.id x) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.vertexEquiv x y t) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.vertexEquiv x y s)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y).Edge s t :=
  SSet.Edge.mk
    { val := h.simplex
      source := by
        simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.front_eq_δ, show Fin.last (1 + 1) = (2 : Fin 3) from by decide,
          constant_one, SSet.Edge.id_edge, SimplicialObject.δ] using h.d₂
      target := by
        rw [lastVertex_one, op_comp, Functor.map_comp_apply]
        change X.δ 0 (X.δ 0 h.simplex) = y
        rw [h.d₀]
        exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.vertexEquiv x y t).tgt_eq }
    (by
      apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex.ext
      change X.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend (SimplexCategory.δ (1 : Fin 2))).op h.simplex = s.val
      rw [extend_δ_one]
      exact h.d₁)
    (by
      apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex.ext
      change X.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend (SimplexCategory.δ (0 : Fin 2))).op h.simplex = t.val
      rw [extend_δ_zero]
      exact h.d₀)

/-- 概要：右 pinched Hom に道があることは始点側が恒等の合成三角形の存在と同値。
方針：同じ二単体を読む二つの構成を存在命題に適用する。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：写像空間の連結成分の関係の同定。 -/
lemma path_iff_compStruct (s t : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y) _⦋0⦌) :
    Nonempty ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y).Edge s t) ↔
      Nonempty (SSet.Edge.CompStruct (SSet.Edge.id x) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.vertexEquiv x y t) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.vertexEquiv x y s)) :=
  ⟨fun ⟨e⟩ => ⟨pathCompStruct e⟩, fun ⟨h⟩ => ⟨pathOfCompStruct h⟩⟩

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
