module
public import SerrePositivity.DifferentialGraded.Quotient.TensorPathCochainExt

/-! # 右tensorした全path直和の任意次数cochainの判定 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma tensorRightPathCochain_ext (S : Set D) (x y : D) (K : Complex A) {T : Complex A} (p : ℤ)
    (f g : Cochain (internalHom A D S x y ⊗ K) T p)
    (h : ∀ w : Word S, (Cochain.ofHom (ι A D S x y w ▷ K)).comp f (zero_add p) =
      (Cochain.ofHom (ι A D S x y w ▷ K)).comp g (zero_add p)) : f = g := by
  apply Cochain.ext
  intro i n hn
  let ev := HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) i
  apply (isColimitOfPreserves ev
    (tensorRightCoproductIsColimit K (fun w : Word S => term A D w x y))).hom_ext
  rintro ⟨w⟩
  change (ι A D S x y w ▷ K).f i ≫ f.v i n hn =
    (ι A D S x y w ▷ K).f i ≫ g.v i n hn
  simpa only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v] using
    congrArg (fun z : Cochain (term A D w x y ⊗ K) T p => z.v i n hn) (h w)

end SerrePositivity.DifferentialGraded.DGQuotient
