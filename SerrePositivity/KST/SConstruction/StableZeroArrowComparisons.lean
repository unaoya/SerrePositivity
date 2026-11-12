module
public import SerrePositivity.KST.SConstruction.StableZeroArrowLoop

/-!
概要：零完全関手からの区間全比較は、指定された両端成分で一意となる。
方針：二比較の差を自己比較にし、両端恒等の零区間自己比較の消滅を適用する。
規約：比較先の図式は任意で、元の二つの全関手同型を保持する。
使われ方：実右面の上下全比較の共有対角の同じ類への照合。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet InfinityCategories LocalizingInvariants
open scoped Simplicial

/-- 概要：全零完全関手の辺からの二つの全比較は、両端の指定成分が等しければ等しい。
方針：比較の差の辺代表を取り、両端恒等の自己比較が恒等であることを使う。
規約：全区間の FunctorIso の等号。使われ方：上下二胞体比較の対角を揃える。 -/
lemma stableZeroArrowFunctorIso_ext (A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B)
    (hF : ∀ x, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (F.hom.app (Opposite.op ⦋0⦌) x))
    {g : (Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u}}
    (e₀ e₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow F).edge) g)
    (h₀ : (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u})
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))).toFunctor.map e₀.hom =
        (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u})
          (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))).toFunctor.map e₁.hom)
    (h₁ : (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u})
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))).toFunctor.map e₀.hom =
        (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u})
          (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))).toFunctor.map e₁.hom) : e₀ = e₁ := by
  let δ := e₀.hom ≫ e₁.inv
  obtain ⟨e, he⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective _ _ δ
  let E₀ := (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u})
    (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))).toFunctor
  let E₁ := (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u})
    (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))).toFunctor
  have hd₀ : E₀.map δ = 𝟙 _ :=
    (E₀.map_comp e₀.hom e₁.inv).trans
      ((congrArg (fun k => k ≫ E₀.map e₁.inv) h₀).trans (E₀.mapIso e₁).hom_inv_id)
  have hd₁ : E₁.map δ = 𝟙 _ :=
    (E₁.map_comp e₀.hom e₁.inv).trans
      ((congrArg (fun k => k ≫ E₁.map e₁.inv) h₁).trans (E₁.mapIso e₁).hom_inv_id)
  have hc₀ : SSet.Truncated.HomotopyCategory.homMk (e.map ((truncation 2).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u}) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))))) =
        SSet.Truncated.HomotopyCategory.homMk (SSet.Truncated.Edge.id _) := by
    change E₀.map (SSet.Truncated.HomotopyCategory.homMk e) = _
    exact (congrArg E₀.map he).trans
      (hd₀.trans (SSet.Truncated.HomotopyCategory.homMk_id _).symm)
  have hc₁ : SSet.Truncated.HomotopyCategory.homMk (e.map ((truncation 2).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u}) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))))) =
        SSet.Truncated.HomotopyCategory.homMk (SSet.Truncated.Edge.id _) := by
    change E₁.map (SSet.Truncated.HomotopyCategory.homMk e) = _
    exact (congrArg E₁.map he).trans
      (hd₁.trans (SSet.Truncated.HomotopyCategory.homMk_id _).symm)
  have hz := stableZeroArrowLoop_homMk_eq_id A B F hF e hc₀ hc₁
  have hd : δ = 𝟙 _ := he.symm.trans
    (hz.trans (SSet.Truncated.HomotopyCategory.homMk_id _))
  apply Iso.ext
  apply (cancel_mono e₁.inv).1
  exact hd.trans e₁.hom_inv_id.symm
end SerrePositivity.KST.SConstruction
