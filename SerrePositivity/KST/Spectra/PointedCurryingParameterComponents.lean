module

public import SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensorVertices
public import SerrePositivity.KST.Spectra.PointedHomotopyClasses

/-!
概要：任意の点つきパラメータで curry と内部 Hom の後合成が元の成分を保つ。
方針：内部 Hom の反復 curry の同型を頂点で計算し、元の評価射へ前合成する。
規約：円や有限パラメータに限定しない。使われ方：符号付き loop の全 Hom の構造条件。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.PointedMapping

/-- 任意のパラメータの curry の頂点は、反復内部 Hom の元の同型による像。 -/
lemma familyVertex_curry {K A V : PointedSimplicialSet.{u}} (f : K ⊗ A ⟶ V) :
    familyVertex (curry f) =
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso K A V).hom.right.app (Opposite.op ⦋0⦌) (familyVertex f) := by
  have h := congrArg (PointedSimplicialSet.unitVertexEquiv _)
    (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensorVertices.curry'_hom f)
  rw [PointedSimplicialSet.unitVertexEquiv_naturality] at h
  exact (familyVertex_eq_pointedHomVertex _).trans
    (h.symm.trans (congrArg _ (familyVertex_eq_pointedHomVertex _).symm))

/-- 任意の点つきパラメータについて curry は全写像族の成分の等式を保持する。 -/
lemma componentOf_curry {K A V : PointedSimplicialSet.{u}} {f g : K ⊗ A ⟶ V}
    (h : componentOf f = componentOf g) : componentOf (curry f) = componentOf (curry g) := by
  have he := congrArg (mapπ₀ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso K A V).hom.right) h
  simpa only [componentOf, mapπ₀_mk, familyVertex_curry] using he

/-- 元の内部 Hom の標的変数への作用は、元の点つき射の成分の等式を保持する。 -/
lemma componentOf_ihom_map (A : PointedSimplicialSet.{u}) {U V : PointedSimplicialSet.{u}}
    {f g : U ⟶ V} (h : componentOf f = componentOf g) :
    componentOf ((ihom A).map f) = componentOf ((ihom A).map g) := by
  have hc := componentOf_curry (componentOf_comp_left h ((ihom.ev A).app U))
  have he (p : U ⟶ V) : curry ((ihom.ev A).app U ≫ p) = (ihom A).map p := by
    rw [curry_natural_right, ← uncurry_id_eq_ev, curry_uncurry, Category.id_comp]
  rw [he f, he g] at hc
  exact hc

end SerrePositivity.KST.Spectra.PointedMapping
