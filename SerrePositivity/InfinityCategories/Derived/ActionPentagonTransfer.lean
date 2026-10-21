module
public import SerrePositivity.InfinityCategories.Derived.FunctorIsoPrecompositionReflection
public import SerrePositivity.InfinityCategories.F2.FunctorIsoWhiskerCancellation
/-!
概要：指定五角式を、同じ共通比較と終辺の自然性を保って元の経路へ移す。
方針：同じ水平比較を前置し、同じ末尾の指定同型を消去する。
規約：指定値と全関手同型を保つ。使われ方：元の導来 kernel 五角式。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
noncomputable section
/-- 同じ三重比較と終辺の自然性は、対応する五角式を元の前合成後の経路へ移す。 -/
lemma pentagonComparison_transfer {X A Y B : SSet.{u}}
    (L : X ⟶ A) (M : Y ⟶ B) (S T U : A ⟶ B) (G H K : X ⟶ Y)
    (xT : FunctorIso (L ≫ T) (H ≫ M)) (xU : FunctorIso (L ≫ U) (K ≫ M))
    (nL nR : FunctorIso (L ≫ S) (G ≫ M))
    (cL : FunctorIso S T) (cR : FunctorIso S U)
    (aL : FunctorIso G H) (aR : FunctorIso G K)
    (e : FunctorIso U T) (e₀ : FunctorIso K H)
    (hl : cL.precomp L ≪≫ xT = nL ≪≫ aL.postcomp M)
    (hr : cR.precomp L ≪≫ xU = nR ≪≫ aR.postcomp M)
    (hn : nL = nR) (ht : xU ≪≫ e₀.postcomp M = e.precomp L ≪≫ xT)
    (hp : aL = aR ≪≫ e₀) : cL.precomp L = FunctorIso.precomp (cR ≪≫ e) L := by
  have hh : cL.precomp L ≪≫ xT = FunctorIso.precomp (cR ≪≫ e) L ≪≫ xT := by
    calc
      _ = nL ≪≫ aL.postcomp M := hl
      _ = nR ≪≫ FunctorIso.postcomp (aR ≪≫ e₀) M := by rw [hn, hp]
      _ = (nR ≪≫ aR.postcomp M) ≪≫ e₀.postcomp M := by
        rw [F2.functorIso_postcomp_trans, Iso.trans_assoc]
      _ = (cR.precomp L ≪≫ xU) ≪≫ e₀.postcomp M := by rw [← hr]
      _ = cR.precomp L ≪≫ (e.precomp L ≪≫ xT) := by rw [Iso.trans_assoc, ht]
      _ = _ := by rw [F2.functorIso_precomp_trans, Iso.trans_assoc]
  apply Iso.ext
  exact (cancel_mono xT.hom).mp (congrArg Iso.hom hh)
end
end SerrePositivity.InfinityCategories
