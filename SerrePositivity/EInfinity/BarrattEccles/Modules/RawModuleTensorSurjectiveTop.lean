module
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorElementLinear

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorSurjectiveTop

/-!
概要：全射な非単射作用素で制限した元の普遍 cochain の最上位成分は零である。
方針：全射は終端を保つので、元の非単射再添字式の後合成は恒等射となる。
規約：元の実成分を保ち、恒等射以外の後合成は取り消さない。
使われ方：退化を含む cone 成分の全自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open _root_.SerrePositivity.ComplexLimits
open scoped Simplicial
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)
lemma strictRawModuleTensorElementLinear_top_surjective_noninjective {m n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (θ : ⦋m⦌ ⟶ ⦋n⦌) (hs : Function.Surjective θ.toOrderHom)
    (hn : ¬Function.Injective θ.toOrderHom) (k : ℤ)
    (hk : k = 1 - ((Finset.univ : Finset (Fin (m + 1))).card : ℤ)) :
    (strictRawModuleTensorElementLinear A X P Q
      ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)).val.component
        Finset.univ k Finset.univ_nonempty hk = 0 := by
  have hlast := _root_.SerrePositivity.ComplexLimits.simplexSurjective_last θ hs
  have hn' : ¬Set.InjOn θ.toOrderHom
      ((Finset.univ : Finset (Fin (m + 1))) : Set (Fin (m + 1))) := by
    simpa only [Finset.coe_univ, Set.injOn_univ] using hn
  have hz := strictRawModuleTensorElementLinear_component_not_inj A X P Q c θ
    Finset.univ k Finset.univ_nonempty hk hn'
  have ht : ∀ (i : Fin (n + 1)) (h : i = Fin.last n)
      (v : GradedHom A (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P)) (ForgetEnrichment.to (Complex A) ((strictRawModuleTensorElementDiagram A X P Q).obj (c.obj i))) k),
      (eHomWhiskerLeft (Complex A) ((strictRawModuleProbeFunctor A X).obj P) ((strictRawModuleTensorElementDiagram A X P Q).map
        (c.map (homOfLE (Fin.le_last i))))).f k v = 0 → v = 0 := by
    intro i h v hv
    subst i
    simp only [homOfLE_refl, CategoryTheory.Functor.map_id] at hv
    rw [eHomWhiskerLeft_id] at hv
    exact hv

  exact ht _ hlast _ hz

end SerrePositivity.EInfinity.BarrattEccles
