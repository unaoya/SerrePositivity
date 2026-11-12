module
public import SerrePositivity.KST.NonConnective.DGKappaConeStrictImageMorita
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleCompactEquivalence
public import SerrePositivity.DifferentialGraded.Derived.FunctorExtensionAdjunction

/-!
概要：Morita 実延長を代表化した同じ cone 関手が、商の perfect 集合を保存・反映する。
方針：射影的源の計算同型と保持した実像同型を、主導来 Morita 同値の perfect 判定へ渡す。
規約：perfect 代表を cone の基底へ追加しない。元の実 cone 関手と集合を保持する。
使われ方：K-7 e の Morita 射の商への下降で、零化する元の実核を照合する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R]
  (C D : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C]
  [DGCategory R D] [Small.{u} D] (f : DGFunctor R C D)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R C κ) (J : DGKappaConeInput R D κ)
  (e : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.DGModuleStrictImage R C D (dgModuleExtension R C D f) I.objects J.objects)

/-- 元の射影的加群の導来延長は、同じ代表化 cone 像の主導来値と同型。 -/
def dgKappaConeStrictImageClassicalIso (M : DGKappaCone R C I) :
    (dgDerivedExtension R C D f).obj ((moduleToDerived R C).obj M.val) ≅
      (moduleToDerived R D).obj ((e.functor R C D _ I.objects J.objects).obj M).val :=
  dgDerivedExtensionResolutionComputation R C D f
    (moduleIdentityProjectiveResolution R C M.val (I.projective M.val M.property)) ≪≫
      (moduleToDerived R D).mapIso (e.iso M)

/-- 主導来 Morita 射の同じ cone 作用は、元の perfect 集合を保存・反映する。 -/
theorem dgKappaConeStrictImage_perfect_iff
    [(dgDerivedExtension R C D f).IsEquivalence] (M : DGKappaCone R C I) :
    (e.functor R C D _ I.objects J.objects).obj M ∈ dgKappaConePerfectObjects R D J ↔
      M ∈ dgKappaConePerfectObjects R C I := by
  let E := (dgDerivedExtension R C D f).asEquivalence
  let : E.functor.Additive := by
    change (dgDerivedExtension R C D f).Additive
    exact dgDerivedExtension_additive R C D f
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModulePerfect_equivalence_iff R C D E ((moduleToDerived R C).obj M.val)
  have hM := dgKappaConeStrictImageClassicalIso R C D f I J e M
  constructor
  · intro hx
    exact h.mp ((modulePerfect R D).prop_of_iso hM.symm hx)
  · intro hx
    exact (modulePerfect R D).prop_of_iso hM (h.mpr hx)

end SerrePositivity.KST.NonConnective
