module
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
概要：BK重みの単体を元の射列と終頂点から評価先への射に分解する。
方針：over圏の射列の台を忘れ、終頂点の構造射を取り出して厳密に往復する。
規約：IS-W2 R03aの細胞表示の証明分割。モデル構造を仮定しない。
使われ方：最後の射について自由な境界細胞による射影cofibrancy。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DiagramModel.BousfieldKanCells
open CategoryTheory Limits
open scoped Simplicial
variable (I : Type u) [SmallCategory I]

/-- 固定次数の自由細胞の元は、射列とその終頂点から評価先への射。 -/
abbrev SimplexData (n : ℕ) (i : I) :=
  Σ c : ComposableArrows I n, (c.obj (Fin.last n) ⟶ i)

/-- 同じ元の射列と最後の射から、over圏の全射列を復元する。 -/
def overSimplex {n : ℕ} {i : I} (s : SimplexData I n i) :
    ComposableArrows (Over i) n where
  obj a := Over.mk (s.1.map (homOfLE (Fin.le_last a)) ≫ s.2)
  map {a b} f := Over.homMk (s.1.map f) (by
    change s.1.map f ≫ (s.1.map (homOfLE (Fin.le_last b)) ≫ s.2) = _
    rw [← Category.assoc, ← s.1.map_comp]
    rfl)
  map_id a := by
    apply Over.OverMorphism.ext
    exact s.1.map_id a
  map_comp f g := by
    apply Over.OverMorphism.ext
    exact s.1.map_comp f g

/-- over射列の台と最後の構造射を回収する。 -/
def simplexData {n : ℕ} {i : I} (s : ComposableArrows (Over i) n) :
    SimplexData I n i := ⟨s ⋙ Over.forget i, (s.obj (Fin.last n)).hom⟩

/-- 復元したover射列の各対象は元の同じ対象。 -/
theorem overSimplex_simplexData_obj {n : ℕ} {i : I}
    (s : ComposableArrows (Over i) n) (a : Fin (n+1)) :
    (overSimplex I (simplexData I s)).obj a = s.obj a := by
  change Over.mk ((s.map (homOfLE (Fin.le_last a))).left ≫
    (s.obj (Fin.last n)).hom) = s.obj a
  exact congrArg Over.mk (Over.w (s.map (homOfLE (Fin.le_last a))))

/-- over射列を分解して復元すると、全射列そのものが戻る。 -/
theorem overSimplex_simplexData {n : ℕ} {i : I}
    (s : ComposableArrows (Over i) n) : overSimplex I (simplexData I s) = s := by
  refine CategoryTheory.Functor.ext (overSimplex_simplexData_obj I s) ?_
  intro a b f
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, Over.eqToHom_left, eqToHom_refl,
    Category.id_comp, Category.comp_id]
  rfl

/-- 分解し直すと、元の同じ射列と最後の射が戻る。 -/
theorem simplexData_overSimplex {n : ℕ} {i : I} (s : SimplexData I n i) :
    simplexData I (overSimplex I s) = s := by
  rcases s with ⟨c, f⟩
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  change c.map (homOfLE (Fin.le_last (Fin.last n))) ≫ f = f
  simp

/-- BK重みの全単体は、最後の射について自由な同じ表示に全単射。 -/
def simplexEquiv (n : ℕ) (i : I) :
    ComposableArrows (Over i) n ≃ SimplexData I n i where
  toFun := simplexData I
  invFun := overSimplex I
  left_inv := overSimplex_simplexData I
  right_inv := simplexData_overSimplex I

/-- 評価先の射で運ぶと、元の射列を保持して最後の射だけが後合成される。 -/
theorem simplexData_postcomp {n : ℕ} {i j : I} (f : i ⟶ j)
    (s : ComposableArrows (Over i) n) :
    simplexData I (s ⋙ Over.map f) =
      ⟨(simplexData I s).1, (simplexData I s).2 ≫ f⟩ := rfl

end SerrePositivity.DiagramModel.BousfieldKanCells
