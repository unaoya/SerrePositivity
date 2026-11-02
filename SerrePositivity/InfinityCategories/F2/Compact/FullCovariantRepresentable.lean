module

public import SerrePositivity.InfinityCategories.F2.Compact.FullCoslicePullback
public import SerrePositivity.InfinityCategories.F1B.Compact.RepresentableCoslice

/-!
概要：全部分包含後の元の全共変 Hom は、元の部分圏内の同じ全 Hom と自然同型。
方針：元の coslice の厳密な底変換を、同じ分類関手で比較する。
規約：値ごとの写像空間同値だけで代用しない。
使われ方：包含が保存する余極限についての compact 性の移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Compact

/-- 元の全部分包含に沿う、元の全共変表現可能関手の全自然比較。 -/
def fullSubcomplexCovariantIso {X : SSet.{u}} [Quasicategory X]
    (P : X _⦋0⦌ → Prop) (x : (fullSubcomplexOnVertices X P) _⦋0⦌) :
    FunctorIso
      ((SSet.uliftFunctor.{u + 1, u}).map (fullSubcomplexOnVertices X P).ι ≫
        covariantRepresentableInfinity ((fullSubcomplexOnVertices X P).ι.app _ x))
      (covariantRepresentableInfinity x) := by
  let i := (fullSubcomplexOnVertices X P).ι
  let p := sliceUnderProjection (SSet.yonedaEquiv.symm x)
  let q := sliceUnderProjection (SSet.yonedaEquiv.symm x ≫ i)
  have : LeftFibration (pullback.snd q i) :=
    ⟨leftFibrations.pullback_snd q i (LeftFibration.mem (p := q))⟩
  let h := (fullSliceUnder_isPullback P (SSet.yonedaEquiv.symm x)).flip
  have e : FunctorIso (covariantRepresentableInfinity (i.app _ x))
      (leftStraighteningInfinityDiagram q) := by
    have he : SSet.yonedaEquiv.symm x ≫ i = SSet.yonedaEquiv.symm (i.app _ x) :=
      SSet.yonedaEquiv_symm_comp x i
    change FunctorIso _ (leftStraighteningInfinityDiagram
      (sliceUnderProjection (SSet.yonedaEquiv.symm x ≫ i)))
    rw [he]
    exact covariantRepresentableInfinity_cosliceIso (i.app _ x)
  exact FunctorIso.precomp e ((SSet.uliftFunctor.{u + 1, u}).map i) ≪≫
    leftStraighteningInfinityDiagram_baseChangeIso q i ≪≫
    (leftClassification_overIso p (pullback.snd q i)
      h.isoPullback h.isoPullback_hom_snd).symm ≪≫
    (covariantRepresentableInfinity_cosliceIso x).symm

end SerrePositivity.InfinityCategories.F2.Compact
