module
public import SerrePositivity.DifferentialGraded.Quotient.PathCochainExt

/-! # 任意次数のpath cochainの全直和への貼合せ -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 閉性を仮定せず、各pathの任意次数cochainを全直和からのcochainへ貼り合わせる。 -/
def pathCochainDesc (S : Set D) (x y : D) (T : Complex A) (p : ℤ)
    (f : ∀ w : Word S, Cochain (term A D w x y) T p) :
    Cochain (internalHom A D S x y) T p :=
  Cochain.mk (fun i n hn =>
    (isColimitOfHasCoproductOfPreservesColimit
      (HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) i)
      (fun w : Word S => term A D w x y)).desc
        (Cofan.mk (T.X n) (fun w => (f w).v i n hn)))

lemma pathCochainDesc_precomp (S : Set D) (x y : D) (T : Complex A) (p : ℤ)
    (f : ∀ w : Word S, Cochain (term A D w x y) T p) (w : Word S) :
    (Cochain.ofHom (ι A D S x y w)).comp (pathCochainDesc A D S x y T p f) (zero_add p) = f w := by
  apply Cochain.ext
  intro i n hn
  rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, pathCochainDesc, Cochain.mk_v]
  exact (isColimitOfHasCoproductOfPreservesColimit
    (HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) i)
    (fun w : Word S => term A D w x y)).fac
      (Cofan.mk (T.X n) (fun w => (f w).v i n hn)) ⟨w⟩

lemma pathCochainDesc_unique (S : Set D) (x y : D) (T : Complex A) (p : ℤ)
    (f : ∀ w : Word S, Cochain (term A D w x y) T p)
    (g : Cochain (internalHom A D S x y) T p)
    (hg : ∀ w, (Cochain.ofHom (ι A D S x y w)).comp g (zero_add p) = f w) :
    g = pathCochainDesc A D S x y T p f := by
  apply pathCochain_ext A D S x y p
  intro w
  rw [hg, pathCochainDesc_precomp]

end SerrePositivity.DifferentialGraded.DGQuotient
