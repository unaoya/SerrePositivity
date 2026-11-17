module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementRowReindex
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic

/-!
概要：barの退化作用素は、元の始点の係数を型の移送以外に変えない。
方針：全射の単調写像は零を零へ送り、元の係数の射はeqToHomとなる。
規約：任意の全射作用素を扱い、基本退化だけには制限しない。
使われ方：IS-W2 R03f.2の退化成分の相対latchingへの分離。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open CategoryTheory SSet
variable {I : Type u} [SmallCategory I] (F : I ⥤ SSet.{u})

/-- 全射の単調写像は、元の最初の頂点を保つ。 -/
theorem simplicialReplacement_epi_zero {m n : SimplexCategory} (α : m ⟶ n) [Epi α] :
    α.toOrderHom 0 = 0 := by
  obtain ⟨i, hi⟩ := (SimplexCategory.epi_iff_surjective.mp (inferInstance : Epi α)) 0
  apply le_antisymm
  · exact hi ▸ α.toOrderHom.monotone (Fin.zero_le i)
  · exact Fin.zero_le _

/-- 同じ全射作用素で制限した基底射列の始点は、元の同じ始点である。 -/
theorem simplicialReplacement_epi_first {m n : SimplexCategory} (α : m ⟶ n) [Epi α]
    (σ : ComposableArrows I n.len) :
    (α.toOrderHom.monotone.functor ⋙ σ).obj 0 = σ.obj 0 :=
  congrArg σ.obj (simplicialReplacement_epi_zero α)

/-- 退化での係数の輸送は、同じ始点の等式に沿う型の移送である。 -/
theorem simplicialReplacement_epi_coefficient {m n : SimplexCategory} (α : m ⟶ n) [Epi α]
    (σ : ComposableArrows I n.len) :
    F.map (σ.map (homOfLE (Fin.zero_le (α.toOrderHom 0)))) =
      eqToHom (congrArg (fun i => F.obj (σ.obj i)) (simplicialReplacement_epi_zero α).symm) := by
  have h : homOfLE (Fin.zero_le (α.toOrderHom 0)) =
      eqToHom (simplicialReplacement_epi_zero α).symm := Subsingleton.elim _ _
  rw [h, eqToHom_map, eqToHom_map]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
