module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorIsoPrecompositionReflection
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoWhiskerCancellation
/-!
概要：指定五角式を、同じ共通比較と終辺の自然性を保って元の経路へ移す。
方針：同じ水平比較を前置し、同じ末尾の指定同型を消去する。
規約：指定値と全関手同型を保つ。使われ方：元の導来 kernel 五角式。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
noncomputable section
/-- 同じ三重比較と終辺の自然性は、対応する五角式を元の前合成後の経路へ移す。 -/
lemma pentagonComparison_transfer {X A Y B : SSet.{u}}
    (L : X ⟶ A) (M : Y ⟶ B) (S T U : A ⟶ B) (G H K : X ⟶ Y)
    (xT : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (L ≫ T) (H ≫ M)) (xU : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (L ≫ U) (K ≫ M))
    (nL nR : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (L ≫ S) (G ≫ M))
    (cL : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso S T) (cR : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso S U)
    (aL : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso G H) (aR : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso G K)
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso U T) (e₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso K H)
    (hl : cL.precomp L ≪≫ xT = nL ≪≫ aL.postcomp M)
    (hr : cR.precomp L ≪≫ xU = nR ≪≫ aR.postcomp M)
    (hn : nL = nR) (ht : xU ≪≫ e₀.postcomp M = e.precomp L ≪≫ xT)
    (hp : aL = aR ≪≫ e₀) : cL.precomp L = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (cR ≪≫ e) L := by
  have hh : cL.precomp L ≪≫ xT = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (cR ≪≫ e) L ≪≫ xT := by
    calc
      _ = nL ≪≫ aL.postcomp M := hl
      _ = nR ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (aR ≪≫ e₀) M := by rw [hn, hp]
      _ = (nR ≪≫ aR.postcomp M) ≪≫ e₀.postcomp M := by
        rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_trans, Iso.trans_assoc]
      _ = (cR.precomp L ≪≫ xU) ≪≫ e₀.postcomp M := by rw [← hr]
      _ = cR.precomp L ≪≫ (e.precomp L ≪≫ xT) := by rw [Iso.trans_assoc, ht]
      _ = _ := by rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_trans, Iso.trans_assoc]
  apply Iso.ext
  exact (cancel_mono xT.hom).mp (congrArg Iso.hom hh)
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
