module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewisePairingRegular
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.PairingKanExtension
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.JoinCells

/-!
概要：edgewise の右延長領域上の Kan 値図式の延長。
方針：構成した正則 pairing をホーンセル分解の延長補題へ適用し、標準単体表示の同型で戻す。
規約：境界の図式の接合はこの延長補題とは別に確認する。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、右端射影の充填の存在の中心となる延長。

対応節は Kerodon 8.1（Tag 03JB）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

/-- 概要：標準単体内の edgewise の右延長領域から Kan 複体への図式は全標準単体へ延長する。
方針：頂点集合から構成した非退化単体の正則 pairing のホーンセル分解を使う。
規約：部分領域上での一致は厳密な等式。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、右射影の境界充填に必要な有限な延長定理。 -/
lemma exists_edgewiseRightExtensionDomain_extension {K : SSet.{u}} [KanComplex K] (n : ℕ)
    (f : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightExtensionDomain n : SSet.{u}) ⟶ K) :
    ∃ F : (Δ[n + n + 1] : SSet.{u}) ⟶ K, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightExtensionDomain n).ι ≫ F = f :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.exists_extension_of_regularPairing (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseExtensionPairing n) f

/-- 概要：edgewise の余単体的重みの中に右延長領域を表示する。
方針：標準単体の領域を重みの標準同型で引き戻す。
規約：左右の因子と反転の規約は既存の edgewiseWeight と一致する。
使われ方：Kerodon Notation 8.1.1.6（Tag 03JK）、境界図式と右半分を接合する実際の重みの領域。 -/
def edgewiseRightWeightDomain (n : ℕ) : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.{u}.obj ⦋n⦌).Subcomplex :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightExtensionDomain n).preimage (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso n).hom

/-- 概要：実際の edgewise 重みの右延長領域から Kan 複体への図式は重み全体へ延長する。
方針：同型に沿う部分複体の逆像の同型で標準単体へ運び、延長した射を重みに戻す。
規約：領域上の等式を保つ。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、右射影の各面と右半分を固定する延長への適用。 -/
lemma exists_edgewiseRightWeightDomain_extension {K : SSet.{u}} [KanComplex K] (n : ℕ)
    (f : (edgewiseRightWeightDomain n : SSet.{u}) ⟶ K) :
    ∃ F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.obj ⦋n⦌ ⟶ K, (edgewiseRightWeightDomain n).ι ≫ F = f := by
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.subcomplexPreimageIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightExtensionDomain n) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso n)
  obtain ⟨F, hF⟩ := exists_edgewiseRightExtensionDomain_extension n (e.inv ≫ f)
  refine ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso n).hom ≫ F, ?_⟩
  calc
    _ = e.hom ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightExtensionDomain n).ι ≫ F := by rfl
    _ = e.hom ≫ e.inv ≫ f := by rw [hF]
    _ = f := by rw [← Category.assoc, e.hom_inv_id, Category.id_comp]

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
