module

public import SerrePositivity.InfinityCategories.F1.VertexFiberIsoProjection
public import SerrePositivity.InfinityCategories.Core.EquivalencePathIso
public import SerrePositivity.InfinityCategories.F1.FullyFaithfulFunctorIsoCoherence

/-!
概要：既存の trivial Kan fibration の二つの持ち上げの比較は、射影後に元の等号へ戻る。
方針：元の比較の fiber 内の同型を同じ射影へ写し、定値写像の像を計算する。
規約：既存の比較同型を選び直さない。
使われ方：大域の元の Hom 自然性と局所の共有頂点三角形の coherence。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 元の持ち上げの比較同型を射影すると、指定した同じ可換等式の同型となる。 -/
lemma functorIsoOfTrivialKanFibration_postcomp {A E B : SSet.{u}}
    (p : E ⟶ B) [TrivialKanFibration p] (f g : A ⟶ E) (h : f ≫ p = g ≫ p) :
    (functorIsoOfTrivialKanFibration p f g h).postcomp p =
      eqToIso (congrArg (fun v : A ⟶ B ↦ SSet.HomotopyCategory.mk (functorVertex v)) h) := by
  let q := (ihom A).map p
  let b := functorVertex (g ≫ p)
  have hc := vertexFiber_isContractibleKan q b
  have := hc.kanComplex
  let v0 : (vertexFiber q b) _⦋0⦌ := ⟨functorVertex f, by
    rw [pinchedConstant_zero]
    change functorVertex (f ≫ p) = functorVertex (g ≫ p)
    rw [h]⟩
  let v1 : (vertexFiber q b) _⦋0⦌ := ⟨functorVertex g, by
    rw [pinchedConstant_zero]
    rfl⟩
  let e := terminalVertexIso (hc.isTerminalVertex v0) (hc.isTerminalVertex v1)
  have hh := congrArg Iso.hom (VertexIso.map_vertexFiber_projection q b e)
  apply Iso.ext
  change (FunctorIso.postcomp (show FunctorIso f g from VertexIso.map e (vertexFiberι q b)) p).hom = _
  simp only [FunctorIso.postcomp, Iso.trans_hom, Iso.symm_hom, eqToIso.hom, eqToIso.inv,
    eqToHom_refl, Category.id_comp, Category.comp_id, CategoryTheory.Functor.mapIso_hom]
  simp only [Iso.trans_hom, Iso.symm_hom, eqToIso.hom, eqToIso.inv, eqToHom_trans] at hh
  exact hh

/-- 既存の fiber 内比較は、同じ等式の充満忠実な後合成による標準逆像そのもの。 -/
lemma functorIsoOfTrivialKanFibration_eq_preimage {A E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (p : E ⟶ B) [TrivialKanFibration p]
    (f g : A ⟶ E) (h : f ≫ p = g ≫ p) :
    functorIsoOfTrivialKanFibration p f g h =
      (isFullyFaithful_of_trivialKanFibration p).preimageFunctorIso
        (eqToIso (congrArg
          (fun v : A ⟶ B ↦ SSet.HomotopyCategory.mk (functorVertex v)) h)) := by
  apply (isFullyFaithful_of_trivialKanFibration p).postcomp_functorIso_injective
  rw [functorIsoOfTrivialKanFibration_postcomp,
    IsFullyFaithful.preimageFunctorIso_postcomp]

end SerrePositivity.InfinityCategories
