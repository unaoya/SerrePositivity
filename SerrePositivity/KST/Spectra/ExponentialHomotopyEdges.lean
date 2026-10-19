module

public import SerrePositivity.KST.Spectra.FibrationEdgeComposition
public import SerrePositivity.KST.Spectra.UnbasedHomotopyIsomorphism

/-!
概要：通常の実ホモトピーを指数写像空間の実辺へ移し、同じ区間として評価し直す。
方針：curry と Yoneda の面の式で端点と源の制限を厳密に計算する。
規約：源と標的の Kan 性は不要。使われ方：指定射影つき合成による正方形の境界修正。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.ExponentialPaths

/-- 通常の射の、零次定数パラメータによる指数写像空間の頂点。 -/
def vertex {A E : SSet.{u}} (f : A ⟶ E) : ((ihom A).obj E) _⦋0⦌ :=
  SSet.yonedaEquiv (curry (fst A (Δ[0] : SSet.{u}) ≫ f))

/-- 定数パラメータ族の curry は、元の射の同じ頂点で一定。 -/
lemma curry_fst {A E T : SSet.{u}} (f : A ⟶ E) :
    curry (fst A T ≫ f) = SSet.const (X := T) (vertex f) := by
  calc
    _ = stdSimplex.isTerminalObj₀.from T ≫ curry (fst A (Δ[0] : SSet.{u}) ≫ f) := by
      rw [← curry_natural_left, ← Category.assoc]
      rfl
    _ = stdSimplex.isTerminalObj₀.from T ≫ SSet.const (vertex f) := by
      rw [← SSet.yonedaEquiv_symm_zero (vertex f), vertex, Equiv.symm_apply_apply]
    _ = _ := SSet.comp_const _ _

variable {A E : SSet.{u}} {f g : A ⟶ E} (H : SSet.Homotopy f g)

/-- ホモトピーの始辺を curry しても、元の射の同じ零次族。 -/
lemma curry_zero : stdSimplex.δ (1 : Fin 2) ≫ curry H.h =
    SSet.yonedaEquiv.symm (vertex f) := by
  have hi : A ◁ stdSimplex.δ (1 : Fin 2) = fst A (Δ[0] : SSet.{u}) ≫ SSet.ι₀ := by
    rw [stdSimplex.δ_one_eq_const]
    rfl
  rw [← curry_natural_left, hi, Category.assoc, H.h₀, vertex, Equiv.symm_apply_apply]

/-- ホモトピーの終辺も、元の同じ終点射の零次族。 -/
lemma curry_one : stdSimplex.δ (0 : Fin 2) ≫ curry H.h =
    SSet.yonedaEquiv.symm (vertex g) := by
  have hi : A ◁ stdSimplex.δ (0 : Fin 2) = fst A (Δ[0] : SSet.{u}) ≫ SSet.ι₁ := by
    rw [stdSimplex.δ_zero_eq_const]
    rfl
  rw [← curry_natural_left, hi, Category.assoc, H.h₁, vertex, Equiv.symm_apply_apply]

/-- 同じホモトピーを、指数写像空間の実際の辺として読む。 -/
def edge : ((ihom A).obj E).Edge (vertex f) (vertex g) :=
  SSet.Edge.mk (SSet.yonedaEquiv (curry H.h))
    (by rw [← stdSimplex.yonedaEquiv_δ_comp, curry_zero, Equiv.apply_symm_apply])
    (by rw [← stdSimplex.yonedaEquiv_δ_comp, curry_one, Equiv.apply_symm_apply])

/-- 辺のパラメータ族は、元の同じホモトピーの curry。 -/
lemma edge_path : SSet.yonedaEquiv.symm (edge H).edge = curry H.h :=
  Equiv.symm_apply_apply _ _

/-- 源への制限は、元の同じホモトピー全体への制限として計算される。 -/
lemma edge_path_pre {B : SSet.{u}} (i : B ⟶ A) :
    SSet.yonedaEquiv.symm (edge H).edge ≫ (MonoidalClosed.pre i).app E =
      curry (i ▷ (Δ[1] : SSet.{u}) ≫ H.h) := by
  rw [edge_path, curry_pre_app]

/-- 指数写像空間の頂点の源への制限は、元の射の同じ前合成。 -/
lemma vertex_pre {B : SSet.{u}} (i : B ⟶ A) (f : A ⟶ E) :
    ((MonoidalClosed.pre i).app E).app _ (vertex f) = vertex (i ≫ f) := by
  rw [vertex, ← SSet.yonedaEquiv_comp, curry_pre_app, whiskerRight_fst_assoc]
  rfl

/-- 指定された二射の間の指数写像空間の辺を、元の実ホモトピーへ評価する。 -/
def homotopyOfEdge (e : ((ihom A).obj E).Edge (vertex f) (vertex g)) :
    SSet.Homotopy f g where
  h := uncurry (SSet.yonedaEquiv.symm e.edge)
  h₀ := by
    have hi : (SSet.ι₀ : A ⟶ _) =
        lift (𝟙 A) (stdSimplex.isTerminalObj₀.from A) ≫
          A ◁ stdSimplex.δ (1 : Fin 2) := rfl
    rw [hi, Category.assoc, ← uncurry_natural_left,
      SSet.Edge.δ_one_yonedaEquiv_symm, vertex, Equiv.symm_apply_apply, uncurry_curry,
      ← Category.assoc, lift_fst, Category.id_comp]
    rfl
  h₁ := by
    have hi : (SSet.ι₁ : A ⟶ _) =
        lift (𝟙 A) (stdSimplex.isTerminalObj₀.from A) ≫
          A ◁ stdSimplex.δ (0 : Fin 2) := rfl
    rw [hi, Category.assoc, ← uncurry_natural_left,
      SSet.Edge.δ_zero_yonedaEquiv_symm, vertex, Equiv.symm_apply_apply, uncurry_curry,
      ← Category.assoc, lift_fst, Category.id_comp]
    rfl
  rel := by ext m ⟨⟨s, hs⟩, r⟩; exact hs.elim

/-- 実ホモトピーを指数辺へ移して戻しても、同じ区間全体が戻る。 -/
lemma homotopyOfEdge_edge_h : (homotopyOfEdge (edge H)).h = H.h := by
  change uncurry (SSet.yonedaEquiv.symm (edge H).edge) = _
  rw [edge_path, uncurry_curry]

end SerrePositivity.KST.Spectra.ExponentialPaths
