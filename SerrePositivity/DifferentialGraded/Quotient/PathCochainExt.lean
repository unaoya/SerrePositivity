module
public import SerrePositivity.DifferentialGraded.Quotient.PathUniversal
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex

/-! # 全path直和を始域とする任意次数cochainの包含による判定 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 閉性を仮定せず、全path直和のcochainを各pathへの制限で判定する。 -/
lemma pathCochain_ext (S : Set D) (x y : D) {T : Complex A} (p : ℤ)
    (f g : Cochain (internalHom A D S x y) T p)
    (h : ∀ w : Word S, (Cochain.ofHom (ι A D S x y w)).comp f (zero_add p) =
      (Cochain.ofHom (ι A D S x y w)).comp g (zero_add p)) : f = g := by
  apply Cochain.ext
  intro i n hn
  let ev := HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) i
  apply (isColimitOfPreserves ev
    (colimit.isColimit (Discrete.functor (fun w : Word S => term A D w x y)))).hom_ext
  intro w
  change (ι A D S x y w.as).f i ≫ f.v i n hn =
    (ι A D S x y w.as).f i ≫ g.v i n hn
  simpa only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v] using
    congrArg (fun z : Cochain (term A D w.as x y) T p => z.v i n hn) (h w.as)

end SerrePositivity.DifferentialGraded.DGQuotient
