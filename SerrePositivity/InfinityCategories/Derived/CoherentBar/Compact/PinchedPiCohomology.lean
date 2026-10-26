module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.ModulePiHomology
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.PinchedMooreNaturality
public import SerrePositivity.InfinityCategories.Derived.ComplexPinchedModel
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory AlgebraicTopology DifferentialGraded DoldKanComparison
open SerrePositivity.KST.Spectra
open scoped Simplicial
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]

/-- 任意の実 pinched 頂点を基点とする、同じ Hom の負次数コホモロジー表示。 -/
def dgBarCompactPinchedPiCohomologyEquiv (x y : D) (n : ℕ)
    (z : (DGNerve.pinchedHom R D x y) _⦋0⦌) :
    KanHomotopyGroup (DGNerve.pinchedHom R D x y) n z ≃*
      Multiplicative ((homObject R D x y).homology (-((n + 1 : ℕ) : ℤ))) :=
  (kanHomotopyGroupIsoEquiv (pinchedHomModuleForgetIso (S := R) x y).symm n z).trans
    ((dgBarCompactModulePiHomologyEquiv (pinchedHomModule (S := R) x y) n
      ((pinchedHomModuleForgetIso (S := R) x y).inv.app _ z)).trans
        ((additiveGroupToMultiplicativeEquiv
          (pinchedHomMooreHomologyIso x y (n + 1)).toLinearEquiv.toAddEquiv).trans
            (additiveGroupToMultiplicativeEquiv (ULift.moduleEquiv (R := R)).toAddEquiv)))

/-- 任意複体の実単位 Hom 模型の全基点を、元の複体の H^{-n-1} へ同定する。 -/
def dgBarCompactComplexPinchedPiCohomologyEquiv (K : Complex R) (n : ℕ)
    (z : (complexPinchedSpace.{u, v} K) _⦋0⦌) :
    KanHomotopyGroup (complexPinchedSpace.{u, v} K) n z ≃*
      Multiplicative (K.homology (-((n + 1 : ℕ) : ℤ))) :=
  (dgBarCompactPinchedPiCohomologyEquiv (complexPinchedSource K)
    (complexPinchedTarget K) n z).trans
      (additiveGroupToMultiplicativeEquiv
        ((HomologicalComplex.homologyFunctor _ _ (-((n + 1 : ℕ) : ℤ))).mapIso
          (complexUnitHomIso K).symm).toLinearEquiv.toAddEquiv)

/-- 零次も同じ Moore 比較を通して元の Hom の H⁰ へ送る。 -/
def dgBarCompactPinchedPiZeroCohomologyEquiv (x y : D) :
    SSet.π₀ (DGNerve.pinchedHom R D x y) ≃ (homObject R D x y).homology 0 :=
  ({ toFun := SSet.mapπ₀ (pinchedHomModuleForgetIso (S := R) x y).inv
     invFun := SSet.mapπ₀ (pinchedHomModuleForgetIso (S := R) x y).hom
     left_inv := by
       intro a
       rw [← SSet.mapπ₀_comp_apply, Iso.inv_hom_id, SSet.mapπ₀_id_apply]
     right_inv := by
       intro a
       rw [← SSet.mapπ₀_comp_apply, Iso.hom_inv_id, SSet.mapπ₀_id_apply] } :
      SSet.π₀ (DGNerve.pinchedHom R D x y) ≃
        SSet.π₀ (moduleUnderlyingSSet (pinchedHomModule (S := R) x y))).trans
    ((modulePiZeroMooreEquiv (pinchedHomModule (S := R) x y)).trans
      ((pinchedHomMooreHomologyIso x y 0).toLinearEquiv.toEquiv.trans
        (ULift.moduleEquiv (R := R)).toEquiv))

/-- 任意複体の実 pinched 模型の連結成分と、元の複体の H⁰。 -/
def dgBarCompactComplexPinchedPiZeroCohomologyEquiv (K : Complex R) :
    SSet.π₀ (complexPinchedSpace.{u, v} K) ≃ K.homology 0 :=
  (dgBarCompactPinchedPiZeroCohomologyEquiv (complexPinchedSource K)
    (complexPinchedTarget K)).trans
      ((HomologicalComplex.homologyFunctor _ _ (0 : ℤ)).mapIso
        (complexUnitHomIso K).symm).toLinearEquiv.toEquiv

end SerrePositivity.InfinityCategories
