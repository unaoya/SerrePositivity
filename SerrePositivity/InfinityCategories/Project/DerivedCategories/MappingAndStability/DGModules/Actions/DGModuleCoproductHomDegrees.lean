module
public import SerrePositivity.DifferentialGraded.Module.Hom.ColimitsAndRightHom
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
/-!
概要：加群余積からの全 Hom を、各次数で元の Hom の直積へ同定する。
方針：実 Hom 複体の余積比較を次数評価し、加群圏の標準直積と比較する。
規約：同じ包含による全次数の制限を保持し、有限性・compact 性は仮定しない。
使われ方：D-8 c5 の native 余積の全単体比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
variable {J : Type u}

def dgModuleCoproductHomDegreeIso (M : J → ModuleCategory R D) (N : ModuleCategory R D)
    (k : ℤ) :
    (moduleCoproductHomFan R D M N).pt.X k ≅
      ModuleCat.of R (∀ j, ((moduleCoproductHomFamily R D M N) j).X k) :=
  (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) k).mapIso
    (moduleCoproductHomIso R D M N) ≪≫
  PreservesProduct.iso (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) k)
    (moduleCoproductHomFamily R D M N) ≪≫
  ModuleCat.piIsoPi _

lemma dgModuleCoproductHomDegreeIso_π (M : J → ModuleCategory R D)
    (N : ModuleCategory R D) (k : ℤ) (j : J) :
    (dgModuleCoproductHomDegreeIso R D M N k).hom ≫
      ModuleCat.ofHom (LinearMap.proj j) =
        (eHomWhiskerRight (Complex R) (Sigma.ι M j) N).f k := by
  simp only [dgModuleCoproductHomDegreeIso, Iso.trans_hom, Category.assoc,
    ModuleCat.piIsoPi_hom_ker_subtype, PreservesProduct.iso_hom, piComparison_comp_π]
  exact congrArg (fun f => f.f k) (moduleCoproductHomIso_hom_π R D M N j)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
