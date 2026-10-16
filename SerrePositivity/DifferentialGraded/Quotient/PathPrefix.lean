module
public import SerrePositivity.DifferentialGraded.Quotient.PathUniversal
public import SerrePositivity.DifferentialGraded.Complexes.TensorCoproduct
public import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-! # 先頭Homとεを保持する全path直和への包含 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 前方Homとεをtensorしたpath cofanも余積である。 -/
def prefixPathCofanIsColimit {S : Set D} (b : S) (x y : D) :
    IsColimit (Cofan.mk (homObject A D x b.val ⊗ (epsilonComplex A ⊗ internalHom A D S b.val y))
      (fun w : Word S => (homObject A D x b.val) ◁ ((epsilonComplex A) ◁ ι A D S b.val y w))) :=
  isColimitOfHasCoproductOfPreservesColimit
    (tensorLeft (epsilonComplex A) ⋙ tensorLeft (homObject A D x b.val))
    (fun w : Word S => term A D w b.val y)

/-- 前方Homとεを追加し、全path直和へ入れる内部chain map。 -/
def prefixPath {S : Set D} (b : S) (x y : D) :
    homObject A D x b.val ⊗ (epsilonComplex A ⊗ internalHom A D S b.val y) ⟶
      internalHom A D S x y :=
  (prefixPathCofanIsColimit A D b x y).desc
    (Cofan.mk (internalHom A D S x y) (fun w : Word S => ι A D S x y (b :: w)))

lemma prefixPath_ι {S : Set D} (b : S) (x y : D) (w : Word S) :
    ((homObject A D x b.val) ◁ ((epsilonComplex A) ◁ ι A D S b.val y w)) ≫
      prefixPath A D b x y = ι A D S x y (b :: w) :=
  (prefixPathCofanIsColimit A D b x y).fac
    (Cofan.mk (internalHom A D S x y) (fun w : Word S => ι A D S x y (b :: w))) ⟨w⟩

/-- 前方Homとεをtensorした直和のcochainも各pathへの制限で決まる。 -/
lemma prefixPathCochain_ext {S : Set D} (b : S) (x y : D) {T : Complex A} (p : ℤ)
    (f g : Cochain
      (homObject A D x b.val ⊗ (epsilonComplex A ⊗ internalHom A D S b.val y)) T p)
    (h : ∀ w : Word S,
      (Cochain.ofHom ((homObject A D x b.val) ◁ ((epsilonComplex A) ◁ ι A D S b.val y w))).comp
          f (zero_add p) =
      (Cochain.ofHom ((homObject A D x b.val) ◁ ((epsilonComplex A) ◁ ι A D S b.val y w))).comp
          g (zero_add p)) : f = g := by
  apply Cochain.ext
  intro i n hn
  let ev := HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) i
  apply (isColimitOfPreserves ev (prefixPathCofanIsColimit A D b x y)).hom_ext
  rintro ⟨w⟩
  change ((homObject A D x b.val) ◁ ((epsilonComplex A) ◁ ι A D S b.val y w)).f i ≫
      f.v i n hn =
    ((homObject A D x b.val) ◁ ((epsilonComplex A) ◁ ι A D S b.val y w)).f i ≫ g.v i n hn
  simpa only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v] using
    congrArg (fun z : Cochain (term A D (b :: w) x y) T p => z.v i n hn) (h w)

end SerrePositivity.DifferentialGraded.DGQuotient
