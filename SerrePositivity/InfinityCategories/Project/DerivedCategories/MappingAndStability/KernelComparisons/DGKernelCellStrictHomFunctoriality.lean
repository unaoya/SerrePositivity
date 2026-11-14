module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.KernelComparisons.DGKernelCellModelStrictLift
/-!
概要：指定 strict lift の実 h Fun 射作用の恒等・合成と選択独立性。
方針：指定済みの実射と比較同型の値を保持して照合する。
規約：生の dg 射の関手性や古い homInvIso の三角式は先取りしない。
使われ方：一般 cell 合成の五角式・単位三角式。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet DifferentialGraded
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (D E : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
local notation "DC" => _root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R D
local notation "EC" => _root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R E
variable {P0 P1 : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D}
local notation "p0" => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P0
local notation "p1" => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P1
local notation "Q0" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModel R D E p0
local notation "Q1" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModel R D E p1
local notation "T0" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellResolution R D E p0
local notation "T1" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellResolution R D E p1
def dgKernelCellModelStrictHom (f : P0 ⟶ P1) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModelFunctorHomFunctor R D E).obj P0 ⟶
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModelFunctorHomFunctor R D E).obj P1 :=
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R DC EC (BimoduleCategory.underlying R EC DC Q0) ≫
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R E).hom)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R DC EC (BimoduleCategory.underlying R EC DC Q1) ≫
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R E).hom)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R D).inv
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R DC EC (BimoduleCategory.underlying R EC DC Q0))
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R DC EC (BimoduleCategory.underlying R EC DC Q1))
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R E).hom
          ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R DC EC).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModelStrictLift R D E f)))
lemma dgKernelCellModelStrictHom_eq_map (f : P0 ⟶ P1) :
    dgKernelCellModelStrictHom R D E f = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModelFunctorHomFunctor R D E).map f :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModelFunctorHomFunctor_map_strictLift R D E f).symm
lemma dgKernelCellModelStrictHom_id (P : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D) :
    dgKernelCellModelStrictHom R D E (𝟙 P) =
      𝟙 ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModelFunctorHomFunctor R D E).obj P) :=
  (dgKernelCellModelStrictHom_eq_map R D E (𝟙 P)).trans
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModelFunctorHomFunctor R D E).map_id P)
lemma dgKernelCellModelStrictHom_comp {P2 : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D}
    (f : P0 ⟶ P1) (g : P1 ⟶ P2) :
    dgKernelCellModelStrictHom R D E (f ≫ g) =
      dgKernelCellModelStrictHom R D E f ≫ dgKernelCellModelStrictHom R D E g := by
  calc
    _ = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModelFunctorHomFunctor R D E).map (f ≫ g) :=
      dgKernelCellModelStrictHom_eq_map R D E (f ≫ g)
    _ = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModelFunctorHomFunctor R D E).map f ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModelFunctorHomFunctor R D E).map g :=
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModelFunctorHomFunctor R D E).map_comp f g
    _ = _ := congrArg₂ (fun x y => x ≫ y)
      (dgKernelCellModelStrictHom_eq_map R D E f).symm
      (dgKernelCellModelStrictHom_eq_map R D E g).symm
lemma dgKernelCellModelStrictHom_independent (f : P0 ⟶ P1) (b : Q0 ⟶ Q1)
    (hb : b ≫ (T1).π = (T0).π ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellRestrictionFunctor R D E).map f) :
    dgKernelCellModelStrictHom R D E f =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R DC EC (BimoduleCategory.underlying R EC DC Q0) ≫
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R E).hom)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R DC EC (BimoduleCategory.underlying R EC DC Q1) ≫
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R E).hom)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R D).inv
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R DC EC (BimoduleCategory.underlying R EC DC Q0))
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R DC EC (BimoduleCategory.underlying R EC DC Q1))
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R E).hom
          ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R DC EC).map b)) :=
  (dgKernelCellModelStrictHom_eq_map R D E f).trans
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModelFunctorHomFunctor_map_raw R D E f b hb)
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
