module

public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneSemifreePiComparison
public import SerrePositivity.EInfinity.PowerOperation.NatIsoFullEssentialDescent

/-!
# 既存 D(A) 上の実 V_A と native Sp の π/H 自然同型

DAG XIII §2.2 のスペクトル忘却の比較。元の閉零圏上の同じ全自然同型を、
証明済みの充満・本質的全射性で native なホモトピー圏全体へ降ろす。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.KST.LocalizingInvariants
attribute [local instance] HasDerivedCategory.standard
variable (A : Type u) [CommRing A]

/-- 全 native D(A) 上での π_j V_A ≅ H^{-j} の自然同型。 -/
def eilenbergMacLaneDerivedPiHomologyIso (j : ℤ) :
    (hoFunctor.map (eilenbergMacLaneDerived A)).toFunctor ⋙ SpectrumHo.piFunctor j ≅
      derivedMultiplicativeCohomologyOnHo A j := by
  let Q := dgClosedHoFunctor A (Semifree A)
  haveI : Q.Full := dgClosedHoFunctor_full A (Semifree A)
  haveI : Q.EssSurj := dgClosedHoFunctor_essSurj A (Semifree A)
  exact natIsoOfFullEssSurj Q _ _ (eilenbergMacLaneSemifreePiComparison A j ≪≫
    (semifreeClosedHoMultiplicativeHomologyIso A j).symm)

/-- D79 の界面の次数規約と台の可換加法群に合わせた、全関手の π/H 比較。 -/
def eilenbergMacLaneDerived_homologyIso (i : ℤ) :
    hoMap (eilenbergMacLaneDerived A) ⋙ SpectrumHo.piFunctor (-i) ⋙ CommGrpCat.toAddCommGrp ≅
      additiveCohomologyOnHo A i := by
  have e : (hoMap (eilenbergMacLaneDerived A) ⋙ SpectrumHo.piFunctor (-i)) ⋙
      CommGrpCat.toAddCommGrp ≅
      (additiveCohomologyOnHo A i ⋙ AddCommGrpCat.toCommGrp) ⋙ CommGrpCat.toAddCommGrp := by
    simpa only [derivedMultiplicativeCohomologyOnHo, neg_neg] using
      Functor.isoWhiskerRight (eilenbergMacLaneDerivedPiHomologyIso A (-i)) CommGrpCat.toAddCommGrp
  exact e ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (additiveCohomologyOnHo A i)
      commGroupAddCommGroupEquivalence.counitIso ≪≫
      Functor.rightUnitor _

end SerrePositivity.EInfinity.PowerOperation
