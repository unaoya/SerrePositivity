module
public import SerrePositivity.KST.SConstruction.CoherentOrdinaryPrism
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentStringPrismChains
public import SerrePositivity.KST.SConstruction.CoherentHomotopyPrisms

/-! # 元の二辺の因子分解列は square の標準二三角形
概要：上下の短い因子分解列を prism で表示すると、元の square の標準二単体になる。
方針：元の入力列と時刻の二成分を有限個の頂点と生成射で照合する。
規約：元の prism と標準三角形を保持する。
使われ方：元の K の上下の定数終点値を、指定された二辺の合成へ戻す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 元の下側の二辺の列は、元の square の下辺・右辺の標準三角形そのもの。 -/
lemma coherentLowerPrismDirect_forward {I : Type u} [SmallCategory I] {x y : I} (f : x ⟶ y) :
    (coherentOrdinaryPrismIso.{u, v} I).hom.app (Opposite.op ⦋2⦌)
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerPrismString (coherentArrowStringDirect f)).chain) =
      (SSet.yonedaEquiv.symm (ULift.up (nerve.edgeMk f).edge) ▷
        (Δ[1] : SSet.{max u v})).app (Opposite.op ⦋2⦌)
        (((SSet.Truncated.Edge.CompStruct.compId _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge).tensor
          (SSet.Truncated.Edge.CompStruct.idComp _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge)).simplex) := by
  apply Prod.ext
  · apply ULift.ext
    refine CategoryTheory.Functor.ext (fun i => ?_) ?_
    · fin_cases i <;> rfl
    · intro i j a
      fin_cases i <;> fin_cases j <;>
        simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      all_goals first | rfl | exact (by have h := a.le; omega)
  · apply SSet.stdSimplex.ext
    intro i
    fin_cases i <;> rfl

/-- 元の上側の二辺の列は、元の square の左辺・上辺の標準三角形そのもの。 -/
lemma coherentUpperPrismDirect_forward {I : Type u} [SmallCategory I] {x y : I} (f : x ⟶ y) :
    (coherentOrdinaryPrismIso.{u, v} I).hom.app (Opposite.op ⦋2⦌)
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperPrismString (coherentArrowStringDirect f)).chain) =
      (SSet.yonedaEquiv.symm (ULift.up (nerve.edgeMk f).edge) ▷
        (Δ[1] : SSet.{max u v})).app (Opposite.op ⦋2⦌)
        (((SSet.Truncated.Edge.CompStruct.idComp _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge).tensor
          (SSet.Truncated.Edge.CompStruct.compId _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge)).simplex) := by
  apply Prod.ext
  · apply ULift.ext
    refine CategoryTheory.Functor.ext (fun i => ?_) ?_
    · fin_cases i <;> rfl
    · intro i j a
      fin_cases i <;> fin_cases j <;>
        simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      all_goals first | rfl | exact (by have h := a.le; omega)
  · apply SSet.stdSimplex.ext
    intro i
    fin_cases i <;> rfl

end SerrePositivity.KST.SConstruction
