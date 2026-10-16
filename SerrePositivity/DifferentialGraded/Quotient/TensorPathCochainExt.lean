module
public import SerrePositivity.DifferentialGraded.Quotient.PathCochainExt
public import SerrePositivity.DifferentialGraded.Complexes.TensorCoproduct

/-! # 左tensorした全path直和のcochainの判定 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 左tensorしたpath直和の任意次数cochainも各pathへの制限で判定できる。 -/
lemma tensorLeftPathCochain_ext (S : Set D) (x y : D) (K : Complex A) {T : Complex A} (p : ℤ)
    (f g : Cochain (K ⊗ internalHom A D S x y) T p)
    (h : ∀ w : Word S, (Cochain.ofHom (K ◁ ι A D S x y w)).comp f (zero_add p) =
      (Cochain.ofHom (K ◁ ι A D S x y w)).comp g (zero_add p)) : f = g := by
  apply Cochain.ext
  intro i n hn
  let ev := HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) i
  apply (isColimitOfPreserves ev
    (tensorLeftCoproductIsColimit K (fun w : Word S => term A D w x y))).hom_ext
  rintro ⟨w⟩
  change (K ◁ ι A D S x y w).f i ≫ f.v i n hn =
    (K ◁ ι A D S x y w).f i ≫ g.v i n hn
  simpa only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v] using
    congrArg (fun z : Cochain (K ⊗ term A D w x y) T p => z.v i n hn) (h w)

end SerrePositivity.DifferentialGraded.DGQuotient
