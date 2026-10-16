module
public import SerrePositivity.DifferentialGraded.Tensor.FreeEvaluation
public import SerrePositivity.DifferentialGraded.Tensor.KFlatComplex
public import SerrePositivity.DifferentialGraded.Tensor.KFlatColimits
public import SerrePositivity.DifferentialGraded.Module.FreeSphereShift
public import SerrePositivity.DifferentialGraded.Module.Semifree.Basic

/-! # 自由sphereとsphere-free段階の相対K-flat性 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory
variable (A : Type u) [CommRing A]

/-- 任意整数次数のsphereはA上K-flat。 -/
lemma complexSphere_kFlat (n : ℤ) : complexKFlat A (complexSphere A n) := by
  have h : complexKFlat A ((complexSphere A 0)⟦-n⟧) :=
    complexKFlat_shift A (complexKFlat_unit A) (-n)
  have e : (complexSphere A 0)⟦-n⟧ ≅ complexSphere A n := by
    simpa using complexSphereShiftIso A 0 (-n)
  exact complexKFlat_of_iso A e.symm h

variable (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 任意次数の自由sphereはHom_DのA-flat性を仮定せず相対K-flat。 -/
lemma freeSphere_relativeKFlat (x : D) (n : ℤ) :
    moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) (freeSphere A D x n)) :=
  freeAt_relativeKFlat A D x (complexSphere A n) (complexSphere_kFlat A n)

/-- 実際のsphere-free表示を持つ段階は相対K-flat。添字はambient宇宙から縮小する。 -/
lemma sphereFreePresentation_relativeKFlat {M : ModuleCategory A D}
    (S : ModuleSphereFreePresentation A D M) :
    moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) M) := by
  have := S.smallIndex
  have : HasExactColimitsOfShape (Discrete S.Index) (ModuleCat.{u} A) :=
    HasExactColimitsOfShape.of_domain_equivalence (ModuleCat.{u} A)
      (Discrete.equivalence (equivShrink.{u} S.Index).symm)
  apply moduleRelativeKFlat_of_iso A D S.iso
  exact moduleRelativeKFlat_colimit A D
    (Discrete.functor fun i => freeSphere A D (S.object i) (S.degree i))
    (fun i => freeSphere_relativeKFlat A D (S.object i.as) (S.degree i.as))

end SerrePositivity.DifferentialGraded
