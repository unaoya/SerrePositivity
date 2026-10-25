module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.InverseEquationTransfer
/-!
概要：任意の pinched 線形単体から、全部分集合の方程式を満たす実 HA 単体を作る。
方針：混合集合では二つの昇順列挙に沿って全頂点方程式を移し、純粋な集合では面を使う。
規約：正規化加群の公開型と元の微分を維持する。
使われ方：全写像空間比較の高次逆射。
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
  (hMC : dgCoherentBarMaurerCartan R D F) (N : RightModule R D)

lemma dgCoherentBarInverseRawData_equation_mixed {m n : ℕ}
    (f : DGNerve.PinchedHom.LinearSimplex R (dgCoherentBarNormalizedModule R D F hMC) N m)
    (s : I _⦋n⦌) (K : Finset (Fin (n + 1))) (L : Finset (Fin (m + 1)))
    (hK : K.Nonempty) (hL : L.Nonempty) :
    (dgCoherentBarInverseRawData R D F hMC N f.val s).Equation (dgCoherentBarJoinSubset K L) := by
  let r := K.card - 1
  let l := L.card - 1
  have hcK : K.card = r + 1 := by have := Finset.card_pos.mpr hK; dsimp [r]; omega
  have hcL : L.card = l + 1 := by have := Finset.card_pos.mpr hL; dsimp [l]; omega
  let α := (K.orderEmbOfFin hcK).toOrderHom
  let β := (L.orderEmbOfFin hcL).toOrderHom
  let γ := dgCoherentBarJoinOrderMap α β
  have hiα : Function.Injective α := (K.orderEmbOfFin hcK).injective
  have hiβ : Function.Injective β := (L.orderEmbOfFin hcL).injective
  have hiγ : Function.Injective γ := dgCoherentBarJoinOrderMap_injective α β hiα hiβ
  have hMap := dgCoherentBarInverseRawData_map_of_injective R D F hMC N f.val s α β hiα hiβ
  have hEq := dgCoherentBarInverseRawData_equation_univ R D F hMC N
    (DGNerve.PinchedHom.LinearSimplex.pullback β f) (I.map (SimplexCategory.mkHom α).op s)
  have hImage := dgCoherentBarEquation_image_of_pullback
    (dgCoherentBarInverseRawData R D F hMC N f.val s) γ _ hMap.symm Finset.univ hEq hiγ.injOn
  have hImg : (Finset.univ : Finset (Fin (r + l + 1 + 1))).image γ =
      dgCoherentBarJoinSubset K L := by
    rw [← dgCoherentBarJoinSubset_univ r l, dgCoherentBarJoinSubset_map]
    change dgCoherentBarJoinSubset
      (Finset.univ.image (K.orderEmbOfFin hcK))
      (Finset.univ.image (L.orderEmbOfFin hcL)) = _
    rw [K.image_orderEmbOfFin_univ hcK, L.image_orderEmbOfFin_univ hcL]
  simpa only [hImg] using hImage

lemma dgCoherentBarInverseRawData_equation {m n : ℕ}
    (f : DGNerve.PinchedHom.LinearSimplex R (dgCoherentBarNormalizedModule R D F hMC) N m)
    (s : I _⦋n⦌) (J : Finset (Fin (n + m + 1 + 1))) :
    (dgCoherentBarInverseRawData R D F hMC N f.val s).Equation J := by
  classical
  let K := dgCoherentBarJoinLeftPart n m J
  let L := dgCoherentBarJoinRightPart n m J
  have hSet : dgCoherentBarJoinSubset K L = J := dgCoherentBarJoinSubset_parts n m J
  by_cases hK : K.Nonempty
  · by_cases hL : L.Nonempty
    · simpa only [hSet] using dgCoherentBarInverseRawData_equation_mixed R D F hMC N f s
        K L hK hL
    · have hLE : L = ∅ := Finset.not_nonempty_iff_eq_empty.mp hL
      have hImg : K.image (dgCoherentBarJoinLeft n m) = J := by
        simpa only [hLE, dgCoherentBarJoinSubset, Finset.image_empty, Finset.union_empty] using hSet
      have he := SimplexData.equation_image_of_pullback
        (dgCoherentBarInverseRawData R D F hMC N f.val s) (dgCoherentBarJoinLeft n m)
        (coherentDiagramSimplex F s) (dgCoherentBarInverseRawData_left R D F hMC N f.val s)
        K (dgCoherentBarJoinLeft_injective n m).injOn
      simpa only [hImg] using he
  · have hKE : K = ∅ := Finset.not_nonempty_iff_eq_empty.mp hK
    have hImg : L.image (dgCoherentBarJoinRight n m) = J := by
      simpa only [hKE, dgCoherentBarJoinSubset, Finset.image_empty, Finset.empty_union] using hSet
    have he := SimplexData.equation_image_of_pullback
      (dgCoherentBarInverseRawData R D F hMC N f.val s) (dgCoherentBarJoinRight n m)
      (InfinityCategories.PinchedHom.constant (X := dgNerve R (RightModule R D))
        (Simplex.vertex (A := R) N) m) (dgCoherentBarInverseRawData_right R D F hMC N f.val s)
      L (dgCoherentBarJoinRight_injective n m).injOn
    simpa only [hImg] using he

def dgCoherentBarInverseSimplex {m n : ℕ}
    (f : DGNerve.PinchedHom.LinearSimplex R (dgCoherentBarNormalizedModule R D F hMC) N m)
    (s : I _⦋n⦌) : DGNerve.Simplex R (RightModule R D) (n + m + 1) where
  toSimplexData := dgCoherentBarInverseRawData R D F hMC N f.val s
  equation J a b k hJ ha hb hk :=
    dgCoherentBarInverseRawData_equation R D F hMC N f s J a b k hJ ha hb hk

end SerrePositivity.InfinityCategories
