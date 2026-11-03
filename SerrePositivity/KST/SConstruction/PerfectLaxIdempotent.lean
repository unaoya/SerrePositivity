module
public import SerrePositivity.InfinityCategories.F2.CatInfinity.LaxPullbackColimitConeExistence
public import SerrePositivity.InfinityCategories.F1B.Idempotent.StrongSplittingExistence

/-! # 元の lax pullback の coherent 冪等完備性
概要：両入力が冪等完備なら、同じ実 lax pullback の全 coherent 冪等図式が分裂する。
方針：両成分の強い分裂の絶対余極限を元の lax pullback の余錐として貼り合わせる。
規約：標的の完備性や lax pullback の完備性を仮定しない。使われ方：Tamme の入力。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open F2.Idempotent

/-- 元の全 coherent 冪等図式は、同じ実 lax pullback 内に余極限を持つ。 -/
lemma perfectLaxIdempotent_hasColimit {A B C : SSet.{u}}
    [Quasicategory A] [Quasicategory B] [Quasicategory C]
    (p : A ⟶ C) (q : B ⟶ C) (hA : IsIdempotentComplete A) (hB : IsIdempotentComplete B)
    (r : CoherentIdempotent (F2.laxPullback p q)) : HasColimit r := by
  obtain ⟨sa⟩ := hA (r ≫ F2.laxPullbackFst p q)
  obtain ⟨sb⟩ := hB (r ≫ F2.laxPullbackSnd p q)
  obtain ⟨c, hc, _, _⟩ := F2.exists_colimitCone_laxPullback_with_components p q r
    sa.cocone sb.cocone sa.cocone_isColimit sb.cocone_isColimit
    (sa.postcomposeCocone_isColimit p) (sb.postcomposeCocone_isColimit q)
  exact ⟨c, hc⟩

/-- 元の実 lax pullback の全 coherent 冪等図式は、元の全図式を保って強く分裂する。 -/
lemma perfectLaxPullback_isIdempotentComplete {A B C : SSet.{u}}
    [Quasicategory A] [Quasicategory B] [Quasicategory C]
    (p : A ⟶ C) (q : B ⟶ C) (hA : IsIdempotentComplete A) (hB : IsIdempotentComplete B) :
    IsIdempotentComplete (F2.laxPullback p q) :=
  fun r => strongSplitting_exists_of_hasColimit r (perfectLaxIdempotent_hasColimit p q hA hB r)

end SerrePositivity.KST.SConstruction
