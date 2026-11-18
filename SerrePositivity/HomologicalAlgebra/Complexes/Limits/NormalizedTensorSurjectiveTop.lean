module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorElementUniversalComponents

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
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.SSet
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)
lemma simplexSurjective_last {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) (hs : Function.Surjective θ.toOrderHom) :
    θ.toOrderHom (Fin.last m) = Fin.last n := by
  obtain ⟨i, hi⟩ := hs (Fin.last n)
  apply le_antisymm (Fin.le_last _)
  rw [← hi]
  exact θ.toOrderHom.monotone (Fin.le_last i)

lemma normalizedTensorElementUniversalLinear_top_surjective_noninjective {m n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (θ : ⦋m⦌ ⟶ ⦋n⦌) (hs : Function.Surjective θ.toOrderHom)
    (hn : ¬Function.Injective θ.toOrderHom) (k : ℤ)
    (hk : k = 1 - ((Finset.univ : Finset (Fin (m + 1))).card : ℤ)) :
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementUniversalLinear A X Y
      ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)).val.component
        Finset.univ k Finset.univ_nonempty hk = 0 := by
  have hlast := _root_.SerrePositivity.ComplexLimits.simplexSurjective_last θ hs
  have hn' : ¬Set.InjOn θ.toOrderHom
      ((Finset.univ : Finset (Fin (m + 1))) : Set (Fin (m + 1))) := by
    simpa only [Finset.coe_univ, Set.injOn_univ] using hn
  have hz := _root_.SerrePositivity.ComplexLimits.normalizedTensorElementUniversalLinear_component_not_inj A X Y c θ
    Finset.univ k Finset.univ_nonempty hk hn'
  have ht : ∀ (i : Fin (n + 1)) (h : i = Fin.last n)
      (v : GradedHom A X ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y).obj (c.obj i)) k),
      (homPostcompose X ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y).map
        (c.map (homOfLE (Fin.le_last i))))).f k v = 0 → v = 0 := by
    intro i h v hv
    subst i
    simp only [homOfLE_refl, CategoryTheory.Functor.map_id] at hv
    have hi : homPostcompose X (𝟙 ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y).obj
        (c.obj (Fin.last n)))) = 𝟙 _ := (homFunctor X).map_id _
    rw [hi] at hv
    exact hv
  exact ht _ hlast _ hz

end SerrePositivity.ComplexLimits
