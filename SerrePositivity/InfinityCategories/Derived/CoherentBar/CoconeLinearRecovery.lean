module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeHomSpaceComparison
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeFamilyFactorization
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.JoinSimplexDataExt
/-!
概要：比較射の線形成分から全パラメーター部分単体の Hom と混合 HA 単体を一意に回収する。
方針：次数符号を二回作用させて消し、純粋な面と混合因数分解の一意性を使う。
規約：写像空間の全次数を扱い、零次の一意性で代用しない。
使われ方：全余錐空間の比較射の単射性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))
  (hMC : dgCoherentBarMaurerCartan R D F)
  (y : (dgNerve R (RightModule R D)) _⦋0⦌)

lemma dgCoherentBarCoconeLinearData_subset_recovery {n : ℕ}
    (c d : (coconeMappingSpace F y) _⦋n⦌)
    (h : dgCoherentBarCoconeLinearData R D F hMC y c =
      dgCoherentBarCoconeLinearData R D F hMC y d)
    (J : Finset (Fin (n + 1))) (r : ℕ) (hc : J.card = r + 1) (hJ : J.Nonempty) :
    dgCoherentBarCoconeSubsetParameterHom R D F hMC y c J r hc =
      dgCoherentBarCoconeSubsetParameterHom R D F hMC y d J r hc := by
  have hk : -(r : ℤ) = 1 - (J.card : ℤ) := by rw [hc]; push_cast; omega
  have hRaw := congrArg (fun f : DGNerve.PinchedHom.LinearData R
      (dgCoherentBarNormalizedModule R D F hMC) (dgNerve.vertexEquiv R (RightModule R D) y) n =>
      f.component J (-(r : ℤ)) hJ hk) h
  have hScalar := eq_of_heq ((dgCoherentBarCoconeSubsetHom_heq R D F hMC y c
    J (-(r : ℤ)) hJ hk r hc).symm.trans ((heq_of_eq hRaw).trans
      (dgCoherentBarCoconeSubsetHom_heq R D F hMC y d J (-(r : ℤ)) hJ hk r hc)))
  have hTwice := congrArg (fun z => (r : ℤ).negOnePow • z) hScalar
  simpa only [smul_smul, Int.units_mul_self, one_smul] using hTwice

lemma dgCoherentBarCoconeFamilySimplex_eq_of_linearData {m n : ℕ}
    (c d : (coconeMappingSpace F y) _⦋m⦌)
    (h : dgCoherentBarCoconeLinearData R D F hMC y c =
      dgCoherentBarCoconeLinearData R D F hMC y d) (s : I _⦋n⦌) :
    dgCoherentBarCoconeFamilySimplex R D F y c s =
      dgCoherentBarCoconeFamilySimplex R D F y d s := by
  apply DGNerve.Simplex.ext
  apply dgCoherentBarJoinSimplexData_ext
  · exact congrArg DGNerve.Simplex.toSimplexData
      ((dgCoherentBarCoconeFamilySimplex_left R D F y c s).trans
        (dgCoherentBarCoconeFamilySimplex_left R D F y d s).symm)
  · exact congrArg DGNerve.Simplex.toSimplexData
      ((dgCoherentBarCoconeFamilySimplex_right R D F y c s).trans
        (dgCoherentBarCoconeFamilySimplex_right R D F y d s).symm)
  · intro K L hK hL a b k hJ ha hb hk
    let r := K.card - 1
    let l := L.card - 1
    have hcK : K.card = r + 1 := by have := Finset.card_pos.mpr hK; dsimp [r]; omega
    have hcL : L.card = l + 1 := by have := Finset.card_pos.mpr hL; dsimp [l]; omega
    have hPhi := dgCoherentBarCoconeLinearData_subset_recovery R D F hMC y c d h L l hcL hL
    dsimp only [dgCoherentBarCoconeSubsetParameterHom] at hPhi
    have hRho : dgCoherentBarCoconeFamilyHomAt R D F hMC y
        ((coconeMappingSpace F y).map
          (SimplexCategory.mkHom (L.orderEmbOfFin hcL).toOrderHom).op c) s =
        dgCoherentBarCoconeFamilyHomAt R D F hMC y
          ((coconeMappingSpace F y).map
            (SimplexCategory.mkHom (L.orderEmbOfFin hcL).toOrderHom).op d) s := by
      unfold dgCoherentBarCoconeFamilyHomAt
      rw [hPhi]
    have hC := dgCoherentBarCoconeFamilySimplex_mixed_factorization R D F hMC y
      (r := r) (l := l) c s K L hcK hcL hK a b k hJ ha hb hk
    have hD := dgCoherentBarCoconeFamilySimplex_mixed_factorization R D F hMC y
      (r := r) (l := l) d s K L hcK hcL hK a b k hJ ha hb hk
    rw [hRho] at hC
    exact hC.trans hD.symm

end SerrePositivity.InfinityCategories
