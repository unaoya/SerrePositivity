module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovImageFactorisation
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSourceImageHomology
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraInvariantConnectivity

/-!
概要：元の上段射の実因子分解の中間代数は connective で、源からの射は n-connected。
方針：源の像拡大への準同型な比較で、計算済みの層と元の射の連結度を移す。
規約：元の標的上段への二射の厳密な合成式を保持。使われ方：LT の値の連結度。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {B C : Mon (Complex R)}
  [B.X.IsStrictlyLE 0] [C.X.IsStrictlyLE 0] (f : B ⟶ C) (n : ℤ) (hn : 0 ≤ n)

lemma postnikovImageFactorisationSource_quasiIsoAt (j : ℤ) (hj : -n ≤ j) :
    QuasiIsoAt (postnikovImageFactorisationSource R f n hn).hom j := by
  have := postnikovImageFactorisationComparison_quasiIso R f n hn
  have hc : QuasiIsoAt ((postnikovImageFactorisationSource R f n hn).hom ≫
      (postnikovImageFactorisationComparison R f n hn).hom) j := by
    have he : (postnikovImageFactorisationSource R f n hn).hom ≫
        (postnikovImageFactorisationComparison R f n hn).hom =
          (postnikovSourceImageFactor R f n hn).hom :=
      congrArg Mon.Hom.hom (postnikovImageFactorisationSource_comparison R f n hn)
    rw [he]
    exact postnikovSourceImageFactor_quasiIsoAt R f n hn j hj
  exact quasiIsoAt_of_comp_right (postnikovImageFactorisationSource R f n hn).hom
    (postnikovImageFactorisationComparison R f n hn).hom j

lemma postnikovImageFactorisationSource_groups_bijective (j : ℤ) (hj : j ≤ n) :
    Function.Bijective ((groups R j).map (postnikovImageFactorisationSource R f n hn)).hom :=
  (groups_map_bijective_iff R _ j).2
    (postnikovImageFactorisationSource_quasiIsoAt R f n hn (-j) (by omega))

lemma postnikovImageFactorisationSource_connected :
    IsConnected R (postnikovImageFactorisationSource R f n hn) n :=
  ⟨fun j hj => (postnikovImageFactorisationSource_groups_bijective R f n hn j hj.le).1,
    fun j hj => (postnikovImageFactorisationSource_groups_bijective R f n hn j hj).2⟩

lemma postnikovImageFactorisationObject_isConnective :
    IsConnective R (postnikovImageFactorisationObject R f n hn) := by
  have := postnikovImageFactorisationComparison_quasiIso R f n hn
  have : (postnikovSourceImageExtension R f n hn).X.IsLE 0 :=
    postnikovSourceImageExtension_isConnective R f n hn
  apply (CochainComplex.isLE_iff _ 0).2
  intro j hj
  exact (exactAt_iff_of_quasiIsoAt (postnikovImageFactorisationComparison R f n hn).hom j).2
    (CochainComplex.exactAt_of_isLE _ 0 j hj)

def postnikovImageFactorisationLayerHomologyIso :
    (postnikovImageFactorisationObject R f n hn).X.homology (-(n + 1)) ≅
      image (homologyMap f.hom (-(n + 1))) := by
  have := postnikovImageFactorisationComparison_quasiIso R f n hn
  exact asIso (homologyMap (postnikovImageFactorisationComparison R f n hn).hom (-(n + 1))) ≪≫
    postnikovSourceImageLayerHomologyIso R f n hn

lemma postnikovImageFactorisationObject_homology_zero (j : ℤ) (hj : j < -(n + 1)) :
    IsZero ((postnikovImageFactorisationObject R f n hn).X.homology j) := by
  have := postnikovImageFactorisationComparison_quasiIso R f n hn
  exact (postnikovSourceImageExtension_homology_zero R f n hn j hj).of_iso
    (asIso (homologyMap (postnikovImageFactorisationComparison R f n hn).hom j))

lemma IsKConnective.postnikovImageFactorisationSource_connected
    (Φ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1} ⟶ Sp.{u + 1}) {k : ℤ} (h : IsKConnective R Φ k) (hn' : 1 ≤ n) :
    (∀ j : ℤ, j < n + k →
      Function.Injective (invariantGroupMap R Φ (postnikovImageFactorisationSource R f n hn) j)) ∧
    ∀ j : ℤ, j ≤ n + k →
      Function.Surjective (invariantGroupMap R Φ (postnikovImageFactorisationSource R f n hn) j) :=
  h.2 (postnikov_isConnective R B (n + 1))
    (postnikovImageFactorisationObject_isConnective R f n hn)
    (postnikovImageFactorisationSource R f n hn) n hn'
    (postnikovImageFactorisationSource_groups_bijective R f n hn 0 hn)
    (DGAlgebra.postnikovImageFactorisationSource_connected R f n hn)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite LT "Lemma 2.30" (partial := component) "仮定：可換基礎環上の非正 dg 代数の自然数塔、n≥1（Lean が強い）。結論：Postnikov 切断からレベルごとに連結な左脚とプロ同値な右脚の因子分解。一般の Pro(Alg^cn) の同値表示は範囲外（Lean が弱い）。"] _root_.SerrePositivity.KST.LocalizingInvariants.DGAlgebra.postnikovImageFactorisationSource_connected
