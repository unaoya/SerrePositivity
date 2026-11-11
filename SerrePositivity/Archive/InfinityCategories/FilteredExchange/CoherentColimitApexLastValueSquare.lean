module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitApexLastDiagonalData
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitRawPointDiagonal
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitApexRawEdgeValues
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerAlgebra
/-!
概要：元の最後辺の値因子と raw 対角値の比を、同じ指定正方形で消去する。
方針：元の raw 最後辺値とその逆を相殺し、同じ終点比較の自然性を値へ移す。
規約：元の指定値・全初期値・実中間と実終点を保持する。
使われ方：Ncomp の元の二辺値因子への帰還。
-/

@[expose] public section
open CategoryTheory SSet
open scoped Simplicial
noncomputable section
namespace SerrePositivity.InfinityCategories.F2
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b d)
local notation "s" => coherentColimitApexTriangle B T
local notation "q" => coherentColimitApexCoefficientMap B T
local notation "f'" => q ≫ coherentColimitRawFiberTransport B a
local notation "V₂" => pointedFiberValueTo (coherentColimitApex_raw_two_vertex B T)
local notation "Vlast" => functorIsoOfEq
  (FunctorIso.precomp (coherentColimitApexRawLastValueIso B T) f')
  (Eq.symm (Category.assoc f' (coherentColimitRawFiberTransport B b) V₂)) rfl
/-- 概要：元の終点比較と raw 最後辺値の同じ指定合成。方針：同じ元の因子を保持する。
規約：指定値を再選択しない。使われ方：Ncomp の値因子の回収。 -/
def coherentColimitApexLastValueComposite :=
  (coherentColimitApexPointedTargetEndpointIso B T).postcomp V₂ ≪≫ Vlast
/-- 概要：同じ raw 最後辺値の逆と raw 対角値の比。方針：同じ元の因子を保持する。
規約：指定値を再選択しない。使われ方：Ncomp の値因子の回収。 -/
def coherentColimitApexLastSquareRawValueRatio :=
  Iso.symm Vlast ≪≫ (coherentColimitRawPointDiagonalComparison B b f').postcomp V₂
/-- 概要：同じ中間同型とその逆の因子を消去。方針：同じ元の因子を保持する。
規約：指定値を再選択しない。使われ方：Ncomp の値因子の回収。 -/
private lemma cancel_middle {C : Type*} [Category C] {a b c d : C}
    (L : a ≅ b) (V : b ≅ c) (D : b ≅ d) :
    (L ≪≫ V) ≪≫ (V.symm ≪≫ D) = L ≪≫ D := by
  rw [Iso.trans_assoc, ← Iso.trans_assoc V V.symm D, Iso.self_symm_id, Iso.refl_trans]
/-- 概要：元の最後辺の比を消去すると同じ指定正方形の値へ戻る。方針：同じ元の因子を保持する。
規約：指定値を再選択しない。使われ方：Ncomp の値因子の回収。 -/
lemma coherentColimitApexLastValueComposite_trans_ratio :
    coherentColimitApexLastValueComposite B T ≪≫ coherentColimitApexLastSquareRawValueRatio B T =
      (coherentColimitApexLastDiagonalComparison B T).postcomp V₂ ≪≫
        (coherentColimitApexLastNativeImageIso B T).postcomp V₂ := by
  unfold coherentColimitApexLastValueComposite coherentColimitApexLastSquareRawValueRatio
  refine (cancel_middle _ _ _).trans ?_
  have h := congrArg (fun e => FunctorIso.postcomp e V₂)
    (coherentColimitApexLastSpecified_endpoint_square B T)
  simp only [functorIso_postcomp_trans] at h
  convert h using 1 <;> rfl
end SerrePositivity.InfinityCategories.F2
