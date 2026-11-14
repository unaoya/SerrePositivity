module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.ModulePiHomology
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.PinchedMooreNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.ComplexPinchedModel
/-!
概要：実 pinched 空間の全基点の正次数 π を元の負次数コホモロジーへ同定する。
方針：全基点の加法移送、既存の Moore 同型、単位 Hom 同型を順に用いる。
規約：零基点への制限や対象の Small 仮定を追加しない。
使われ方：coherent bar の評価空間の各頂点に置くホモロジーチャート。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
open CategoryTheory AlgebraicTopology DifferentialGraded
open _root_.SerrePositivity.KST.Spectra
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R D]

/-- 任意の実 pinched 頂点を基点とする、同じ Hom の負次数コホモロジー表示。 -/
def dgBarCompactPinchedPiCohomologyEquiv (x y : D) (n : ℕ)
    (z : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R D x y) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R D x y) n z ≃*
      Multiplicative ((_root_.SerrePositivity.DifferentialGraded.homObject R D x y).homology (-((n + 1 : ℕ) : ℤ))) :=
  (_root_.SerrePositivity.InfinityCategories.HA.Section1_2_3.kanHomotopyGroupIsoEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomModuleForgetIso (S := R) x y).symm n z).trans
    ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactModulePiHomologyEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomModule (S := R) x y) n
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomModuleForgetIso (S := R) x y).inv.app _ z)).trans
        ((_root_.SerrePositivity.InfinityCategories.HA.Section1_2_3.additiveGroupToMultiplicativeEquiv
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomMooreHomologyIso x y (n + 1)).toLinearEquiv.toAddEquiv).trans
            (_root_.SerrePositivity.InfinityCategories.HA.Section1_2_3.additiveGroupToMultiplicativeEquiv (ULift.moduleEquiv (R := R)).toAddEquiv)))

/-- 任意複体の実単位 Hom 模型の全基点を、元の複体の H^{-n-1} へ同定する。 -/
def dgBarCompactComplexPinchedPiCohomologyEquiv (K : Complex R) (n : ℕ)
    (z : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, v} K) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, v} K) n z ≃*
      Multiplicative (K.homology (-((n + 1 : ℕ) : ℤ))) :=
  (dgBarCompactPinchedPiCohomologyEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSource K)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedTarget K) n z).trans
      (_root_.SerrePositivity.InfinityCategories.HA.Section1_2_3.additiveGroupToMultiplicativeEquiv
        ((HomologicalComplex.homologyFunctor _ _ (-((n + 1 : ℕ) : ℤ))).mapIso
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso K).symm).toLinearEquiv.toAddEquiv)

/-- 零次も同じ Moore 比較を通して元の Hom の H⁰ へ送る。 -/
def dgBarCompactPinchedPiZeroCohomologyEquiv (x y : D) :
    SSet.π₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R D x y) ≃ (_root_.SerrePositivity.DifferentialGraded.homObject R D x y).homology 0 :=
  ({ toFun := SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomModuleForgetIso (S := R) x y).inv
     invFun := SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomModuleForgetIso (S := R) x y).hom
     left_inv := by
       intro a
       rw [← SSet.mapπ₀_comp_apply, Iso.inv_hom_id, SSet.mapπ₀_id_apply]
     right_inv := by
       intro a
       rw [← SSet.mapπ₀_comp_apply, Iso.hom_inv_id, SSet.mapπ₀_id_apply] } :
      SSet.π₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R D x y) ≃
        SSet.π₀ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomModule (S := R) x y))).trans
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.modulePiZeroMooreEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomModule (S := R) x y)).trans
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomMooreHomologyIso x y 0).toLinearEquiv.toEquiv.trans
        (ULift.moduleEquiv (R := R)).toEquiv))

/-- 任意複体の実 pinched 模型の連結成分と、元の複体の H⁰。 -/
def dgBarCompactComplexPinchedPiZeroCohomologyEquiv (K : Complex R) :
    SSet.π₀ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, v} K) ≃ K.homology 0 :=
  (dgBarCompactPinchedPiZeroCohomologyEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSource K)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedTarget K)).trans
      ((HomologicalComplex.homologyFunctor _ _ (0 : ℤ)).mapIso
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso K).symm).toLinearEquiv.toEquiv

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
