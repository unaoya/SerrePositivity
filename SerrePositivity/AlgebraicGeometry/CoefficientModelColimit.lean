module

public import SerrePositivity.AlgebraicGeometry.CoefficientModelDiagram
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Types.Filtered

/-!
概要：任意の環写像を、全有限型係数模型の実際の filtered 余極限として表す。
方針：元は一変数多項式で表示し、像が一致する二元は像の模型で一致させる。
規約：元の R,C の有限型性・Noether 性を要求しない。
使われ方：B03・B04 の被覆模型の final な部分圏への移送。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory Limits
universe u
variable {k R C : Type u} [CommRing k] [CommRing R] [CommRing C]
  [Algebra k R] [Algebra k C] (g : R →ₐ[k] C)

/-- 元の基底環の任意の元は、小さい全模型の実際の構造射で表示できる。 -/
theorem coefficientModelSmallBaseCocone_exists_rep (r : R) :
    ∃ (i : CoefficientModelIndex g) (x : (coefficientModelSmallBaseDiagram g).obj i),
      ((coefficientModelSmallBaseCocone g).ι.app i).hom x = r := by
  let P := MvPolynomial (Fin 1) k
  let a : P →ₐ[k] R := MvPolynomial.aeval (fun _ ↦ r)
  let X := coefficientModelObj g (AlgHom.id k P) a (g.comp a) (by ext x; rfl)
  let E := equivSmallModel (CoefficientModelCategory k g)
  let w := E.unitIso.hom.app X
  refine ⟨E.functor.obj X, ((coefficientModelBaseDiagram g).map w).hom (MvPolynomial.X 0), ?_⟩
  have hn := (coefficientModelBaseCocone g).ι.naturality w
  have H := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hn) (MvPolynomial.X 0)
  change (((coefficientModelBaseCocone g).ι.app (E.inverse.obj (E.functor.obj X))).hom
    (((coefficientModelBaseDiagram g).map w).hom (MvPolynomial.X 0))) = a (MvPolynomial.X 0) at H
  exact H.trans (MvPolynomial.aeval_X (R := k) (fun _ : Fin 1 ↦ r) 0)

/-- 元の始域環の任意の元は、小さい全模型の実際の構造射で表示できる。 -/
theorem coefficientModelSmallSourceCocone_exists_rep (c : C) :
    ∃ (i : CoefficientModelIndex g) (x : (coefficientModelSmallSourceDiagram g).obj i),
      ((coefficientModelSmallSourceCocone g).ι.app i).hom x = c := by
  let P := MvPolynomial (Fin 1) k
  let d : P →ₐ[k] C := MvPolynomial.aeval (fun _ ↦ c)
  let X := coefficientModelObj g (Algebra.ofId k P) (Algebra.ofId k R) d (by ext)
  let E := equivSmallModel (CoefficientModelCategory k g)
  let w := E.unitIso.hom.app X
  refine ⟨E.functor.obj X, ((coefficientModelSourceDiagram g).map w).hom (MvPolynomial.X 0), ?_⟩
  have hn := (coefficientModelSourceCocone g).ι.naturality w
  have H := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hn) (MvPolynomial.X 0)
  change (((coefficientModelSourceCocone g).ι.app (E.inverse.obj (E.functor.obj X))).hom
    (((coefficientModelSourceDiagram g).map w).hom (MvPolynomial.X 0))) = d (MvPolynomial.X 0) at H
  exact H.trans (MvPolynomial.aeval_X (R := k) (fun _ : Fin 1 ↦ c) 0)

/-- 同じ構造射で一致する二元は、実際の像の模型へ移すと一致する。 -/
theorem coefficientModelSmallBaseCocone_eq_eventually (i : CoefficientModelIndex g)
    (x y : (coefficientModelSmallBaseDiagram g).obj i)
    (h : ((coefficientModelSmallBaseCocone g).ι.app i).hom x =
      ((coefficientModelSmallBaseCocone g).ι.app i).hom y) :
    ∃ (j : CoefficientModelIndex g) (q : i ⟶ j),
      ((coefficientModelSmallBaseDiagram g).map q).hom x =
        ((coefficientModelSmallBaseDiagram g).map q).hom y := by
  let E : CoefficientModelCategory k g ≌ CoefficientModelIndex g :=
    equivSmallModel (CoefficientModelCategory k g)
  let X := E.inverse.obj i
  let Y := coefficientModelImageObj g X
  let f := coefficientModelToImage g X
  have hxy : ((coefficientModelBaseDiagram g).map f).hom x =
      ((coefficientModelBaseDiagram g).map f).hom y := by
    apply Subtype.ext
    exact h
  let j := E.functor.obj Y
  let w : E.inverse.obj i ⟶ E.inverse.obj j := f ≫ E.unitIso.hom.app Y
  let q : i ⟶ j := E.inverse.preimage w
  have hq : E.inverse.map q = w := E.inverse.map_preimage w
  refine ⟨j, q, ?_⟩
  change ((coefficientModelBaseDiagram g).map (E.inverse.map q)).hom x =
    ((coefficientModelBaseDiagram g).map (E.inverse.map q)).hom y
  rw [hq]
  change ((coefficientModelBaseDiagram g).map (f ≫ E.unitIso.hom.app Y)).hom x =
    ((coefficientModelBaseDiagram g).map (f ≫ E.unitIso.hom.app Y)).hom y
  simp only [Functor.map_comp]
  change ((coefficientModelBaseDiagram g).map (E.unitIso.hom.app Y)).hom
      (((coefficientModelBaseDiagram g).map f).hom x) =
    ((coefficientModelBaseDiagram g).map (E.unitIso.hom.app Y)).hom
      (((coefficientModelBaseDiagram g).map f).hom y)
  exact congrArg ((coefficientModelBaseDiagram g).map (E.unitIso.hom.app Y)).hom hxy

/-- 元の環は、小さい全模型の実際の構造 cocone の filtered colimit。 -/
def coefficientModelSmallBaseCoconeIsColimit : IsColimit (coefficientModelSmallBaseCocone g) := by
  letI : ReflectsColimitsOfShape (CoefficientModelIndex g) (forget CommRingCat.{u}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  apply isColimitOfReflects (forget CommRingCat.{u})
  apply Types.FilteredColimit.isColimitOf'
  · intro x
    obtain ⟨i, y, hy⟩ := coefficientModelSmallBaseCocone_exists_rep g x
    exact ⟨i, y, hy.symm⟩
  · intro i x y h
    obtain ⟨j, q, hq⟩ := coefficientModelSmallBaseCocone_eq_eventually g i x y h
    exact ⟨j, q, hq⟩

/-- 同じ構造射で一致する二元は、実際の像の模型へ移すと一致する。 -/
theorem coefficientModelSmallSourceCocone_eq_eventually (i : CoefficientModelIndex g)
    (x y : (coefficientModelSmallSourceDiagram g).obj i)
    (h : ((coefficientModelSmallSourceCocone g).ι.app i).hom x =
      ((coefficientModelSmallSourceCocone g).ι.app i).hom y) :
    ∃ (j : CoefficientModelIndex g) (q : i ⟶ j),
      ((coefficientModelSmallSourceDiagram g).map q).hom x =
        ((coefficientModelSmallSourceDiagram g).map q).hom y := by
  let E : CoefficientModelCategory k g ≌ CoefficientModelIndex g :=
    equivSmallModel (CoefficientModelCategory k g)
  let X := E.inverse.obj i
  let Y := coefficientModelImageObj g X
  let f := coefficientModelToImage g X
  have hxy : ((coefficientModelSourceDiagram g).map f).hom x =
      ((coefficientModelSourceDiagram g).map f).hom y := by
    apply Subtype.ext
    exact h
  let j := E.functor.obj Y
  let w : E.inverse.obj i ⟶ E.inverse.obj j := f ≫ E.unitIso.hom.app Y
  let q : i ⟶ j := E.inverse.preimage w
  have hq : E.inverse.map q = w := E.inverse.map_preimage w
  refine ⟨j, q, ?_⟩
  change ((coefficientModelSourceDiagram g).map (E.inverse.map q)).hom x =
    ((coefficientModelSourceDiagram g).map (E.inverse.map q)).hom y
  rw [hq]
  change ((coefficientModelSourceDiagram g).map (f ≫ E.unitIso.hom.app Y)).hom x =
    ((coefficientModelSourceDiagram g).map (f ≫ E.unitIso.hom.app Y)).hom y
  simp only [Functor.map_comp]
  change ((coefficientModelSourceDiagram g).map (E.unitIso.hom.app Y)).hom
      (((coefficientModelSourceDiagram g).map f).hom x) =
    ((coefficientModelSourceDiagram g).map (E.unitIso.hom.app Y)).hom
      (((coefficientModelSourceDiagram g).map f).hom y)
  exact congrArg ((coefficientModelSourceDiagram g).map (E.unitIso.hom.app Y)).hom hxy

/-- 元の環は、小さい全模型の実際の構造 cocone の filtered colimit。 -/
def coefficientModelSmallSourceCoconeIsColimit : IsColimit (coefficientModelSmallSourceCocone g) := by
  letI : ReflectsColimitsOfShape (CoefficientModelIndex g) (forget CommRingCat.{u}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  apply isColimitOfReflects (forget CommRingCat.{u})
  apply Types.FilteredColimit.isColimitOf'
  · intro x
    obtain ⟨i, y, hy⟩ := coefficientModelSmallSourceCocone_exists_rep g x
    exact ⟨i, y, hy.symm⟩
  · intro i x y h
    obtain ⟨j, q, hq⟩ := coefficientModelSmallSourceCocone_eq_eventually g i x y h
    exact ⟨j, q, hq⟩

/-- 元の環写像は、小さい全模型の実際の環写像の filtered colimit。 -/
def coefficientModelSmallArrowCoconeIsColimit : IsColimit (coefficientModelSmallArrowCocone g) :=
  Comma.fstSndJointlyReflectColimit (coefficientModelSmallBaseCoconeIsColimit g)
    (coefficientModelSmallSourceCoconeIsColimit g)

/-- 全模型の実際の環写像の cocone も、元の環写像を余極限に持つ。 -/
def coefficientModelArrowCoconeIsColimit : IsColimit (coefficientModelArrowCocone g) :=
  IsColimit.ofWhiskerEquivalence (equivSmallModel (CoefficientModelCategory k g)).symm
    (coefficientModelSmallArrowCoconeIsColimit g)

end SerrePositivity.AlgebraicGeometry
