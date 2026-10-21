module
public import SerrePositivity.InfinityCategories.Derived.ResolutionSourceComparisonComposition
/-!
概要：元の指定出力分解比較は、二段の入力前合成と同じ合成則を満たす。
方針：既存の比較を入力比較の後合成へ同定し、同じ指定入力比較の合成則を使う。
規約：元の定義を変更しない。使われ方：導来 kernel の指定合成子の経路照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
variable {X Y Z A B C V : SSet.{u}} [Quasicategory X] [Quasicategory Y] [Quasicategory Z]
  [Quasicategory A] [Quasicategory B] [Quasicategory C] [Quasicategory V]
/-- 元の二つの指定出力比較は、同じ合成入力写像の指定比較へ厳密に合成される。 -/
lemma qCatResolutionOutputPrecompIso_comp
    (Q : QCatEquivalence X A) (S : QCatEquivalence Y B) (T : QCatEquivalence Z C)
    (h : A ⟶ B) (k : B ⟶ C) (H : X ⟶ Y) (J : Y ⟶ Z)
    (RX : X ⟶ V) (RY : Y ⟶ V) (RZ : Z ⟶ V)
    (hs : H ≫ S.hom = Q.hom ≫ h) (ht : J ≫ T.hom = S.hom ≫ k)
    (hu : (H ≫ J) ≫ T.hom = Q.hom ≫ (h ≫ k))
    (hr : H ≫ RY = RX) (hj : J ≫ RZ = RY) (huR : (H ≫ J) ≫ RZ = RX) :
    qCatResolutionOutputPrecompIso Q T (h ≫ k) (H ≫ J) RX RZ hu huR =
      qCatResolutionOutputPrecompIso Q S h H RX RY hs hr ≪≫
        (qCatResolutionOutputPrecompIso S T k J RY RZ ht hj).precomp h := by
  let d := qCatResolutionSourceComparisonIso Q S h H hs
  let c := qCatResolutionSourceComparisonIso S T k J ht
  let a := qCatResolutionOutputPrecompIso Q S h H RX RY hs hr
  let b := qCatResolutionOutputPrecompIso S T k J RY RZ ht hj
  have ha : HEq a ((d.postcomp J).postcomp RZ) := by
    have h1 := qCatResolutionOutputPrecompIso_sourceComparison_heq Q S h H RX RY hs hr
    have h2 := F2.functorIso_postcomp_heq_of_map_eq d hj
    have h3 := heq_of_eq (F2.functorIso_postcomp_postcomp d J RZ).symm
    exact h1.trans (h2.trans h3)
  have hb : HEq (b.precomp h) ((c.precomp h).postcomp RZ) := by
    have h1 := F2.functorIso_precomp_heq_of_heq (c.postcomp RZ) b
      (congrArg (fun t => S.inv ≫ t) hj) rfl
      (qCatResolutionOutputPrecompIso_sourceComparison_heq S T k J RY RZ ht hj) h
    have h2 := heq_of_eq (F2.functorIso_precomp_postcomp c h RZ).symm
    exact h1.trans h2
  have hp := functorIso_trans_heq a (b.precomp h)
    ((d.postcomp J).postcomp RZ) ((c.precomp h).postcomp RZ)
    (congrArg (fun t => Q.inv ≫ t) huR.symm)
    (congrArg (fun t => h ≫ S.inv ≫ t) hj.symm) rfl ha hb
  have hc := congrArg
    (fun e : FunctorIso (Q.inv ≫ H ≫ J) (h ≫ k ≫ T.inv) => e.postcomp RZ)
    (qCatResolutionSourceComparisonIso_comp Q S T h k H J hs ht hu)
  rw [F2.functorIso_postcomp_trans] at hc
  exact eq_of_heq ((qCatResolutionOutputPrecompIso_sourceComparison_heq
    Q T (h ≫ k) (H ≫ J) RX RZ hu huR).trans ((heq_of_eq hc).trans hp.symm))
end SerrePositivity.InfinityCategories
