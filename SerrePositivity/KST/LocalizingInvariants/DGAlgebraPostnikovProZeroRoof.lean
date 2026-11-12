module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovImageZeroLayer
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovFunctor
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraGroupZeroHomology

/-!
概要：層群の pro 零性から、十分先の元の遷移を源の下段への実準同型を持つ図式で分解。
方針：元に依存しない零遷移を取り、元のホモロジー射の零性を実像拡大へ送る。
規約：実代数射と厳密な二三角形を保持。使われ方：有限 Postnikov 切断の実 pro 比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] (n : ℤ) (hn : 0 ≤ n)

lemma exists_postnikovProZeroRoof (A : Tower (NonpositiveAlgebra R))
    (h : IsProZero ((A.map (nonpositiveInclusion R)).map (groups R (n + 1)))) (i : ℕ) :
    ∃ m, ∃ hi : i ≤ m,
      QuasiIso (postnikovImageFactorisationBaseProjection R (A.transition hi).hom n hn).hom ∧
      postnikovImageFactorisationSource R (A.transition hi).hom n hn ≫
        postnikovImageFactorisationBaseProjection R (A.transition hi).hom n hn =
          postnikovTransition R (A.obj m).obj (n + 1) n (by omega) ∧
      postnikovImageFactorisationSource R (A.transition hi).hom n hn ≫
        postnikovImageFactorisationTarget R (A.transition hi).hom n hn =
          postnikovMap R (A.transition hi).hom (n + 1) := by
  obtain ⟨m, hi, hz⟩ := h i
  have hg : (groups R (n + 1)).map (A.transition hi).hom = 0 := hz
  have hh := homologyMap_eq_zero_of_groups_zero R (A.transition hi).hom (n + 1) hg
  exact ⟨m, hi, postnikovImageFactorisationBaseProjection_quasiIso_of_zero R _ n hn hh,
    postnikovImageFactorisationSource_base R _ n hn, postnikovImageFactorisation_fac R _ n hn⟩

lemma IsKConnective.postnikovImageBase_value_isInvertible
    (Φ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1} ⟶ Sp.{u + 1}) {k : ℤ} (h : IsKConnective R Φ k)
    {B C : Mon (Complex R)} [B.X.IsStrictlyLE 0] [C.X.IsStrictlyLE 0] (f : B ⟶ C)
    (hf : HomologicalComplex.homologyMap f.hom (-(n + 1)) = 0) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (perfectMap R
      (postnikovImageFactorisationBaseProjection R f n hn))).map Φ).toTruncated :=
  h.quasiIso_value_isInvertible R Φ (postnikovImageFactorisationObject_isConnective R f n hn)
    (postnikov_isConnective R B n) (postnikovImageFactorisationBaseProjection R f n hn)
    (postnikovImageFactorisationBaseProjection_quasiIso_of_zero R f n hn hf)

lemma IsKConnective.exists_postnikovProZeroValueRoof
    (Φ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1} ⟶ Sp.{u + 1}) {k : ℤ} (h : IsKConnective R Φ k)
    (A : Tower (NonpositiveAlgebra R))
    (hA : IsProZero ((A.map (nonpositiveInclusion R)).map (groups R (n + 1)))) (i : ℕ) :
    ∃ m, ∃ hi : i ≤ m, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (perfectMap R
      (postnikovImageFactorisationBaseProjection R
        (A.transition hi).hom n hn))).map Φ).toTruncated := by
  obtain ⟨m, hi, hz⟩ := hA i
  have hg : (groups R (n + 1)).map (A.transition hi).hom = 0 := hz
  have hh := homologyMap_eq_zero_of_groups_zero R (A.transition hi).hom (n + 1) hg
  exact ⟨m, hi, h.postnikovImageBase_value_isInvertible R n hn Φ _ hh⟩

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
