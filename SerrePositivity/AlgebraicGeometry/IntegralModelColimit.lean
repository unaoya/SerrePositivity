module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import SerrePositivity.AlgebraicGeometry.IntegralModelFiltered
public import SerrePositivity.AlgebraicGeometry.IntegralFinitePresentationModel

/-!
概要：整代数を、有限かつ有限表示の代数の実際の filtered 余極限として表す。
方針：各元の有限段での表示と一致判定を台の型で示し、可換環へ普遍性を反映する。
規約：模型の構造射と小さい添字を保持し、基底の Noether 性を仮定しない。
使われ方：整拡大の有限表示近似を Spec の逆極限へ渡し、Rydh の細分を有限段へ運ぶ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u
variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]

/-- I03 の共同全射性：整元は小さい模型の実際の構造射で表せる。 -/
theorem integralModelSmallCocone_exists_rep [Algebra.IsIntegral R B] (b : B) :
    ∃ (i : IntegralModelIndex R B) (x : (integralModelSmallDiagram R B).obj i),
      ((integralModelSmallCocone R B).ι.app i).hom x = b := by
  obtain ⟨C, _, _, hCfin, hCfp, g, hg⟩ :=
    exists_finite_finitePresentation_model_of_integral_family (R := R) (B := B)
      1 (fun _ : Fin 1 ↦ b) (fun _ ↦ Algebra.IsIntegral.isIntegral (R := R) b)
  letI : Module.Finite R C := hCfin
  letI : Algebra.FinitePresentation R C := hCfp
  obtain ⟨c, hc⟩ := hg 0
  let X := integralModelObj g
  let E := equivSmallModel (IntegralModelCategory R B)
  let a := E.unitIso.hom.app X
  refine ⟨E.functor.obj X, ((integralModelDiagram R B).map a).hom c, ?_⟩
  have hn := (integralModelCocone R B).ι.naturality a
  have hnc := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hn) c
  change (((integralModelCocone R B).ι.app (E.inverse.obj (E.functor.obj X))).hom
      (((integralModelDiagram R B).map a).hom c)) = g c at hnc
  exact hnc.trans hc

/-- I03 の一致判定：同じ構造射で一致する元は、後の模型でも一致する。 -/
theorem integralModelSmallCocone_eq_eventually (i : IntegralModelIndex R B)
    (x y : (integralModelSmallDiagram R B).obj i)
    (h : ((integralModelSmallCocone R B).ι.app i).hom x =
      ((integralModelSmallCocone R B).ι.app i).hom y) :
    ∃ (j : IntegralModelIndex R B) (f : i ⟶ j),
      ((integralModelSmallDiagram R B).map f).hom x =
        ((integralModelSmallDiagram R B).map f).hom y := by
  classical
  let E : IntegralModelCategory R B ≌ IntegralModelIndex R B :=
    equivSmallModel (IntegralModelCategory R B)
  let X := E.inverse.obj i
  let C : Type u := X.obj.left.obj
  letI : CommRing C := inferInstanceAs (CommRing X.obj.left.obj)
  letI : Algebra R C := inferInstanceAs (Algebra R X.obj.left.obj)
  letI : Module.Finite R C := X.property.1
  letI : Algebra.FinitePresentation R C := X.property.2
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
  let Z := integralModelObj k
  let f : X ⟶ Z := integralModelHomMk q (Ideal.Quotient.liftₐ_comp J g _)
  have hq : q x = q y := by
    change Ideal.Quotient.mk J x = Ideal.Quotient.mk J y
    exact Ideal.Quotient.eq.mpr (Ideal.subset_span (Set.mem_singleton_iff.mpr rfl))
  let j := E.functor.obj Z
  let a : E.inverse.obj i ⟶ E.inverse.obj j := f ≫ E.unitIso.hom.app Z
  let φ : i ⟶ j := E.inverse.preimage a
  have hφ : E.inverse.map φ = a := E.inverse.map_preimage a
  refine ⟨j, φ, ?_⟩
  change ((integralModelDiagram R B).map (E.inverse.map φ)).hom x =
    ((integralModelDiagram R B).map (E.inverse.map φ)).hom y
  rw [hφ]
  change ((integralModelDiagram R B).map (f ≫ E.unitIso.hom.app Z)).hom x =
    ((integralModelDiagram R B).map (f ≫ E.unitIso.hom.app Z)).hom y
  simp only [Functor.map_comp]
  change ((integralModelDiagram R B).map (E.unitIso.hom.app Z)).hom (q x) =
    ((integralModelDiagram R B).map (E.unitIso.hom.app Z)).hom (q y)
  exact congrArg ((integralModelDiagram R B).map (E.unitIso.hom.app Z)).hom hq

/-- 整代数 B は、有限・有限表示の実際の模型の cocone の filtered colimit。 -/
def integralModelSmallCoconeIsColimit [Algebra.IsIntegral R B] :
    IsColimit (integralModelSmallCocone R B) := by
  letI : ReflectsColimitsOfShape (IntegralModelIndex R B) (forget CommRingCat.{u}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  apply isColimitOfReflects (forget CommRingCat.{u})
  apply Types.FilteredColimit.isColimitOf'
  · intro b
    obtain ⟨i, x, hx⟩ := integralModelSmallCocone_exists_rep R B b
    exact ⟨i, x, hx.symm⟩
  · intro i x y h
    obtain ⟨j, f, hf⟩ := integralModelSmallCocone_eq_eventually R B i x y h
    exact ⟨j, f, hf⟩

end SerrePositivity.AlgebraicGeometry
