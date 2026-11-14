module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import SerrePositivity.AlgebraicGeometry.FinitePresentationModelFiltered
public import SerrePositivity.AlgebraicGeometry.FinitePresentationModelCoequalizer

/-!
概要：任意の代数を、有限表示の代数の実際の filtered 余極限として表す。
方針：各元の有限段での表示と一致判定を台の型で示し、可換環へ普遍性を反映する。
規約：模型の構造射と小さい添字を保持し、基底の Noether 性を仮定しない。
使われ方：任意の代数の有限表示近似を Spec の逆極限へ渡し、Rydh の細分を有限段へ運ぶ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u
variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]

/-- B04 の共同全射性：元は小さい模型の実際の構造射で表せる。 -/
theorem finitePresentationModelSmallCocone_exists_rep (b : B) :
    ∃ (i : FinitePresentationModelIndex R B) (x : (finitePresentationModelSmallDiagram R B).obj i),
      ((finitePresentationModelSmallCocone R B).ι.app i).hom x = b := by
  let C := MvPolynomial (Fin 1) R
  let g : C →ₐ[R] B := MvPolynomial.aeval (fun _ ↦ b)
  let c : C := MvPolynomial.X 0
  have hc : g c = b := MvPolynomial.aeval_X (R := R) (fun _ : Fin 1 ↦ b) 0
  let X := finitePresentationModelObj g
  let E := equivSmallModel (FinitePresentationModelCategory R B)
  let a := E.unitIso.hom.app X
  refine ⟨E.functor.obj X, ((finitePresentationModelDiagram R B).map a).hom c, ?_⟩
  have hn := (finitePresentationModelCocone R B).ι.naturality a
  have hnc := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hn) c
  change (((finitePresentationModelCocone R B).ι.app (E.inverse.obj (E.functor.obj X))).hom
      (((finitePresentationModelDiagram R B).map a).hom c)) = g c at hnc
  exact hnc.trans hc

/-- B04 の一致判定：同じ構造射で一致する元は、後の模型でも一致する。 -/
theorem finitePresentationModelSmallCocone_eq_eventually (i : FinitePresentationModelIndex R B)
    (x y : (finitePresentationModelSmallDiagram R B).obj i)
    (h : ((finitePresentationModelSmallCocone R B).ι.app i).hom x =
      ((finitePresentationModelSmallCocone R B).ι.app i).hom y) :
    ∃ (j : FinitePresentationModelIndex R B) (f : i ⟶ j),
      ((finitePresentationModelSmallDiagram R B).map f).hom x =
        ((finitePresentationModelSmallDiagram R B).map f).hom y := by
  classical
  let E : FinitePresentationModelCategory R B ≌ FinitePresentationModelIndex R B :=
    equivSmallModel (FinitePresentationModelCategory R B)
  let X := E.inverse.obj i
  let C : Type u := X.obj.left.obj
  letI : CommRing C := inferInstanceAs (CommRing X.obj.left.obj)
  letI : Algebra R C := inferInstanceAs (Algebra R X.obj.left.obj)
  letI : Algebra.FinitePresentation R C := X.property
  let g : C →ₐ[R] B := X.obj.hom.hom
  have hxy : g x = g y := h
  let J : Ideal C := Ideal.span {x - y}
  have hJ : J.FG := ⟨{x - y}, by simp [J]⟩
  have hJker : J ≤ RingHom.ker g.toRingHom := by
    apply Ideal.span_le.mpr
    rintro z rfl
    apply RingHom.mem_ker.mpr
    change g (x - y) = 0
    rw [map_sub, hxy, sub_self]
  let Q := C ⧸ J
  letI : Algebra.FinitePresentation R Q := Algebra.FinitePresentation.quotient hJ
  let q : C →ₐ[R] Q := Ideal.Quotient.mkₐ R J
  let k : Q →ₐ[R] B := Ideal.Quotient.liftₐ J g
    (fun a ha ↦ RingHom.mem_ker.mp (hJker ha))
  let Z := finitePresentationModelObj k
  let f : X ⟶ Z := finitePresentationModelHomMk q (Ideal.Quotient.liftₐ_comp J g _)
  have hq : q x = q y := by
    change Ideal.Quotient.mk J x = Ideal.Quotient.mk J y
    exact Ideal.Quotient.eq.mpr (Ideal.subset_span (Set.mem_singleton_iff.mpr rfl))
  let j := E.functor.obj Z
  let a : E.inverse.obj i ⟶ E.inverse.obj j := f ≫ E.unitIso.hom.app Z
  let φ : i ⟶ j := E.inverse.preimage a
  have hφ : E.inverse.map φ = a := E.inverse.map_preimage a
  refine ⟨j, φ, ?_⟩
  change ((finitePresentationModelDiagram R B).map (E.inverse.map φ)).hom x =
    ((finitePresentationModelDiagram R B).map (E.inverse.map φ)).hom y
  rw [hφ]
  change ((finitePresentationModelDiagram R B).map (f ≫ E.unitIso.hom.app Z)).hom x =
    ((finitePresentationModelDiagram R B).map (f ≫ E.unitIso.hom.app Z)).hom y
  simp only [Functor.map_comp]
  change ((finitePresentationModelDiagram R B).map (E.unitIso.hom.app Z)).hom (q x) =
    ((finitePresentationModelDiagram R B).map (E.unitIso.hom.app Z)).hom (q y)
  exact congrArg ((finitePresentationModelDiagram R B).map (E.unitIso.hom.app Z)).hom hq

/-- 任意の代数 B は、有限表示の実際の模型の cocone の filtered colimit。 -/
def finitePresentationModelSmallCoconeIsColimit :
    IsColimit (finitePresentationModelSmallCocone R B) := by
  letI : ReflectsColimitsOfShape (FinitePresentationModelIndex R B) (forget CommRingCat.{u}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  apply isColimitOfReflects (forget CommRingCat.{u})
  apply Types.FilteredColimit.isColimitOf'
  · intro b
    obtain ⟨i, x, hx⟩ := finitePresentationModelSmallCocone_exists_rep R B b
    exact ⟨i, x, hx.symm⟩
  · intro i x y h
    obtain ⟨j, f, hf⟩ := finitePresentationModelSmallCocone_eq_eventually R B i x y h
    exact ⟨j, f, hf⟩

end SerrePositivity.AlgebraicGeometry
