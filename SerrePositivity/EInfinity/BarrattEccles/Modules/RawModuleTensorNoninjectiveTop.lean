module
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorSurjectiveTop

/-!
概要：任意の非単射作用素で制限した元の普遍 cochain の最上位成分は零である。
方針：元の作用素の実 epi-mono 像分解を使い、全射な非単射作用素の消滅へ戻す。
規約：元の全制限列を厳密に一致させる。使われ方：全退化成分の消滅。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Limits SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open _root_.SerrePositivity.ComplexLimits
open scoped Simplicial
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorElementLinear_top_noninjective {m n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (θ : ⦋m⦌ ⟶ ⦋n⦌) (hn : ¬Function.Injective θ.toOrderHom) (k : ℤ)
    (hk : k = 1 - ((Finset.univ : Finset (Fin (m + 1))).card : ℤ)) :
    (strictRawModuleTensorElementLinear A X P Q
      ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)).val.component
        Finset.univ k Finset.univ_nonempty hk = 0 := by
  let β := factorThruImage θ
  let ι := image.ι θ
  have hs : Function.Surjective β.toOrderHom := SimplexCategory.epi_iff_surjective.mp inferInstance
  have hi : Function.Injective ι.toOrderHom := SimplexCategory.mono_iff_injective.mp inferInstance
  have hβ : ¬Function.Injective β.toOrderHom := by
    intro h
    apply hn
    rw [← image.fac θ]
    exact hi.comp h
  have hz := strictRawModuleTensorElementLinear_top_surjective_noninjective A X P Q
    ((SimplexCategory.toCat.map ι).toFunctor ⋙ c) β hs hβ k hk
  have hcol : (SimplexCategory.toCat.map β).toFunctor ⋙
      ((SimplexCategory.toCat.map ι).toFunctor ⋙ c) =
      (SimplexCategory.toCat.map θ).toFunctor ⋙ c := by
    have hf := congrArg (fun φ : ⦋m⦌ ⟶ ⦋n⦌ =>
      (SimplexCategory.toCat.map φ).toFunctor ⋙ c) (image.fac θ)
    simpa only [CategoryTheory.Functor.map_comp, Cat.Hom.comp_toFunctor,
      CategoryTheory.Functor.assoc] using hf
  have ht : ∀ (c d : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) m) (he : c = d),
      (strictRawModuleTensorElementLinear A X P Q c).val.component
        Finset.univ k Finset.univ_nonempty hk = 0 →
      (strictRawModuleTensorElementLinear A X P Q d).val.component
        Finset.univ k Finset.univ_nonempty hk = 0 := by
    intro c d he h
    subst d
    exact h
  exact ht _ _ hcol hz

end SerrePositivity.EInfinity.BarrattEccles
