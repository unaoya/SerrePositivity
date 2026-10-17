module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.InternalComposition
public import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-! # 先頭Homと任意次数生成元を全path直和に追加する包含 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w) [Small.{u} I]
variable (C : Family A D I)

def prefixCofanIsColimit (i : I) (x y : D) :
    IsColimit (Cofan.mk (homObject A D x (C.source i) ⊗
      (C.generator A D I i ⊗ C.internalHom A D I (C.target i) y))
      (fun w : List I => (homObject A D x (C.source i)) ◁
        ((C.generator A D I i) ◁ C.inclusion A D I w (C.target i) y))) :=
  isColimitOfHasCoproductOfPreservesColimit
    (tensorLeft (C.generator A D I i) ⋙ tensorLeft (homObject A D x (C.source i)))
    (fun w : List I => C.term A D I w (C.target i) y)

def prefixPath (i : I) (x y : D) :
    homObject A D x (C.source i) ⊗ (C.generator A D I i ⊗ C.internalHom A D I (C.target i) y) ⟶
      C.internalHom A D I x y :=
  (C.prefixCofanIsColimit A D I i x y).desc
    (Cofan.mk (C.internalHom A D I x y) (fun w : List I => C.inclusion A D I (i :: w) x y))

lemma prefixPath_inclusion (i : I) (x y : D) (w : List I) :
    ((homObject A D x (C.source i)) ◁
      ((C.generator A D I i) ◁ C.inclusion A D I w (C.target i) y)) ≫
      C.prefixPath A D I i x y = C.inclusion A D I (i :: w) x y :=
  (C.prefixCofanIsColimit A D I i x y).fac
    (Cofan.mk (C.internalHom A D I x y) (fun w : List I => C.inclusion A D I (i :: w) x y)) ⟨w⟩

lemma prefixPathCochain_ext (i : I) (x y : D) {T : Complex A} (p : ℤ)
    (f g : Cochain (homObject A D x (C.source i) ⊗
      (C.generator A D I i ⊗ C.internalHom A D I (C.target i) y)) T p)
    (h : ∀ w : List I,
      (Cochain.ofHom ((homObject A D x (C.source i)) ◁
        ((C.generator A D I i) ◁ C.inclusion A D I w (C.target i) y))).comp f (zero_add p) =
      (Cochain.ofHom ((homObject A D x (C.source i)) ◁
        ((C.generator A D I i) ◁ C.inclusion A D I w (C.target i) y))).comp g (zero_add p)) :
    f = g := by
  apply Cochain.ext
  intro a n hn
  let ev := HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) a
  apply (isColimitOfPreserves ev (C.prefixCofanIsColimit A D I i x y)).hom_ext
  rintro ⟨w⟩
  change ((homObject A D x (C.source i)) ◁
      ((C.generator A D I i) ◁ C.inclusion A D I w (C.target i) y)).f a ≫ f.v a n hn =
    ((homObject A D x (C.source i)) ◁
      ((C.generator A D I i) ◁ C.inclusion A D I w (C.target i) y)).f a ≫ g.v a n hn
  simpa only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v] using
    congrArg (fun z : Cochain (C.term A D I (i :: w) x y) T p => z.v a n hn) (h w)

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
