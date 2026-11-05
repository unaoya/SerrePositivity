module
public import SerrePositivity.KST.SConstruction.TammePerfectSplit

/-! # Tamme の同じ実 Sp 積錐と元の lax 値への可逆辺
概要：同じ lax pullback の分裂を、元の値を終点とする可逆辺と実 ∞ 積錐にする。
方針：元の半直交分解の可逆辺・同じ分裂の類・実積錐をそのまま回収する。
規約：lax pullback の完備性を入力に仮定しない。使われ方：Land–Tamme 主定理。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet Spectra
open SerrePositivity.InfinityCategories LocalizingInvariants
open F2.Idempotent
open scoped Simplicial

/-- 同じ BF スペクトルの単体的圏を使用する。 -/
local instance tammeSplit_simplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

variable {C D B : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap C B) (q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap D B)
  (hC : IsIdempotentComplete C.obj) (hD : IsIdempotentComplete D.obj)
  {F : perfectStableInfinity.{u} ⟶ Sp.{u}} (hF : IsPerfectLocalizingInvariant F)

/-- 同じ元の lax pullback の値を終点とする、実 Sp の分裂辺。 -/
def IsPerfectLocalizingInvariant.tammeSplitEdge : Sp.{u}.Edge
    (coherentNerveVertex (NativeSplit.product
      (hF.sequenceFiberTriangle (tammePerfectSequence p q hC hD))))
    (F.app (Opposite.op ⦋0⦌) (perfectLaxVertex p q hC hD)) :=
  hF.perfectSemiorthogonalSplitEdge (perfectLaxSemiorthogonal p q hC hD)

/-- Tamme の同じ分裂辺は、元の実 Sp の可逆辺。 -/
lemma IsPerfectLocalizingInvariant.tammeSplitEdge_isInvertible :
    IsInvertibleEdge (hF.tammeSplitEdge p q hC hD).toTruncated :=
  hF.perfectSemiorthogonalSplitEdge_isInvertible (perfectLaxSemiorthogonal p q hC hD)

/-- 同じ可逆辺は、元の包含・切断・第一射影を回収する分裂の類を持つ。 -/
lemma IsPerfectLocalizingInvariant.tammeSplitEdge_hom :
    Truncated.HomotopyCategory.homMk (hF.tammeSplitEdge p q hC hD).toTruncated =
      (hF.tammeSplitEquivalence p q hC hD).hom :=
  hF.perfectSemiorthogonalSplitEdge_hom (perfectLaxSemiorthogonal p q hC hD)

/-- 同じ分裂辺の終点は、元の F2 lax pullback の同じ不変量値。 -/
lemma IsPerfectLocalizingInvariant.tammeSplitEdge_target :
    Sp.δ 0 (hF.tammeSplitEdge p q hC hD).edge =
      F.app (Opposite.op ⦋0⦌) (perfectLaxVertex p q hC hD) :=
  (hF.tammeSplitEdge p q hC hD).tgt_eq

/-- 同じ D・C に対応する二因子の、元の実 Sp 積錐。 -/
def IsPerfectLocalizingInvariant.tammeProductCone :=
  hF.perfectSemiorthogonalProductCone (perfectLaxSemiorthogonal p q hC hD)

/-- 同じ元の積錐は、実 Sp の ∞ 極限である。 -/
lemma IsPerfectLocalizingInvariant.tammeProductCone_isLimit :
    IsLimitCone (hF.tammeProductCone p q hC hD) :=
  hF.perfectSemiorthogonalProductCone_isLimit (perfectLaxSemiorthogonal p q hC hD)

/-- 同じ実積錐の頂点は、元の分裂可逆辺の始点の BF 積。 -/
lemma IsPerfectLocalizingInvariant.tammeProductCone_vertex :
    (hF.tammeProductCone p q hC hD).vertex =
      coherentNerveVertex (NativeSplit.product
        (hF.sequenceFiberTriangle (tammePerfectSequence p q hC hD))) :=
  hF.perfectSemiorthogonalProductCone_vertex (perfectLaxSemiorthogonal p q hC hD)

end SerrePositivity.KST.SConstruction
