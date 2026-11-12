module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.AlgebraicTopology.SimplicialSet.Op

/-!
概要：反対圏の射列を単体の順序反転で元の圏の射列へ移す。
方針：射列の順序と矢印を反転し二重反転を消去する。
規約：同じ宇宙の小さい圏を扱う。
使われ方：B5 の左 Kan の局所添字の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Opposite
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison

variable {C : Type u} [Category.{u} C]

/-- 概要：反対圏の可合成射の列の順序と向きを反転する実写像。
方針：rev の反変な順序と unop の合成の逆転を組み合わせる。
規約：通常の圏の反対圏と単体の反転を区別する。
使われ方：反対 nerve の単体ごとの実比較。 -/
def oppositeNerveSimplex {n : ℕ} (F : ComposableArrows Cᵒᵖ n) : ComposableArrows C n where
  obj i := unop (F.obj i.rev)
  map {i j} h := (F.map (homOfLE (Fin.rev_le_rev.mpr (leOfHom h)))).unop
  map_id i := by
    rw [show homOfLE (Fin.rev_le_rev.mpr (leOfHom (𝟙 i))) = 𝟙 i.rev from Subsingleton.elim _ _,
      F.map_id]
    rfl
  map_comp f g := by
    rw [← unop_comp, ← F.map_comp]
    congr 1

/-- 概要：元の圏の列を順序と向きを反転して反対圏へ送る実写像。
方針：rev と op を組み合わせる。
規約：通常の圏の反対圏と単体の反転を区別する。
使われ方：反対 nerve の実比較の逆写像。 -/
def nerveOppositeSimplex {n : ℕ} (F : ComposableArrows C n) : ComposableArrows Cᵒᵖ n where
  obj i := op (F.obj i.rev)
  map {i j} h := (F.map (homOfLE (Fin.rev_le_rev.mpr (leOfHom h)))).op
  map_id i := by
    rw [show homOfLE (Fin.rev_le_rev.mpr (leOfHom (𝟙 i))) = 𝟙 i.rev from Subsingleton.elim _ _,
      F.map_id]
    rfl
  map_comp f g := by
    rw [← op_comp, ← F.map_comp]
    congr 1

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
