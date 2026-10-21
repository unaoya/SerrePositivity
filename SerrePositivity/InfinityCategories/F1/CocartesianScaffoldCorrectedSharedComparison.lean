module

public import SerrePositivity.InfinityCategories.F1.CocartesianScaffoldCorrectedGlobalCoherence

/-!
概要：元の二つの補正成分の指定像を同じ共有頂点の表示へ揃えると厳密に一致する。
方針：元の直接自然性への指定値と両端の回収を組み合わせる。
規約：補正 path と元の大域自然性の指定値を保持する。
使われ方：二成分の同型を同じ pullback の同型へ束ねる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories

variable (n : ℕ) {C : Type u} [Category.{u} C] (k : ULift.{u} (Fin (n + 2)) ⥤ C)
  (p q : CocartesianFibrationCategory (nerve C))

/-- 最初の補正成分の共有頂点への指定像を、端点表示だけ揃えた同型。 -/
def cocartesianScaffoldCorrectedFirstSharedGlobalIso :
    FunctorIso
      (cocartesianBaseChangeHomNaturalityIso (cocartesianScaffoldSharedCell n k) p q).sourceMap
      (cocartesianBaseChangeHomNaturalityIso (cocartesianScaffoldSharedCell n k) p q).targetMap :=
  F2.functorIsoOfEq ((cocartesianScaffoldCorrectedFirstGlobalIso n k p q).postcomp
    ((cocartesianScaffoldLocalTarget n k p q).map WalkingCospan.Hom.inl))
    (cocartesianScaffoldCorrectedFirstGlobalIso_shared_source n k p q)
    (cocartesianScaffoldCorrectedFirstGlobalIso_shared_target n k p q)

/-- 同じ端点へ揃えた最初の指定像は、元の共有頂点の直接自然性そのもの。 -/
lemma cocartesianScaffoldCorrectedFirstSharedGlobalIso_eq :
    cocartesianScaffoldCorrectedFirstSharedGlobalIso n k p q =
    cocartesianBaseChangeHomNaturalityIso (cocartesianScaffoldSharedCell n k) p q := by
  exact eq_of_heq ((F2.functorIsoOfEq_heq
    ((cocartesianScaffoldCorrectedFirstGlobalIso n k p q).postcomp
      ((cocartesianScaffoldLocalTarget n k p q).map WalkingCospan.Hom.inl))
    (cocartesianScaffoldCorrectedFirstGlobalIso_shared_source n k p q)
    (cocartesianScaffoldCorrectedFirstGlobalIso_shared_target n k p q)).trans
    (cocartesianScaffoldCorrectedFirstGlobalIso_shared_heq n k p q))

/-- 次の補正成分の共有頂点への指定像を、端点表示だけ揃えた同型。 -/
def cocartesianScaffoldCorrectedSecondSharedGlobalIso :
    FunctorIso
      (cocartesianBaseChangeHomNaturalityIso (cocartesianScaffoldSharedCell n k) p q).sourceMap
      (cocartesianBaseChangeHomNaturalityIso (cocartesianScaffoldSharedCell n k) p q).targetMap :=
  F2.functorIsoOfEq ((cocartesianScaffoldCorrectedSecondGlobalIso n k p q).postcomp
    ((cocartesianScaffoldLocalTarget n k p q).map WalkingCospan.Hom.inr))
    (cocartesianScaffoldCorrectedSecondGlobalIso_shared_source n k p q)
    (cocartesianScaffoldCorrectedSecondGlobalIso_shared_target n k p q)

/-- 同じ端点へ揃えた次の指定像は、元の共有頂点の直接自然性そのもの。 -/
lemma cocartesianScaffoldCorrectedSecondSharedGlobalIso_eq :
    cocartesianScaffoldCorrectedSecondSharedGlobalIso n k p q =
    cocartesianBaseChangeHomNaturalityIso (cocartesianScaffoldSharedCell n k) p q := by
  exact eq_of_heq ((F2.functorIsoOfEq_heq
    ((cocartesianScaffoldCorrectedSecondGlobalIso n k p q).postcomp
      ((cocartesianScaffoldLocalTarget n k p q).map WalkingCospan.Hom.inr))
    (cocartesianScaffoldCorrectedSecondGlobalIso_shared_source n k p q)
    (cocartesianScaffoldCorrectedSecondGlobalIso_shared_target n k p q)).trans
    (cocartesianScaffoldCorrectedSecondGlobalIso_shared_heq n k p q))

/-- 元の全 Hom 上で、二つの補正成分の共有頂点への指定像は厳密に一致する。 -/
lemma cocartesianScaffoldCorrectedSharedGlobalIso_coherence :
    cocartesianScaffoldCorrectedFirstSharedGlobalIso n k p q =
      cocartesianScaffoldCorrectedSecondSharedGlobalIso n k p q :=
  (cocartesianScaffoldCorrectedFirstSharedGlobalIso_eq n k p q).trans
    (cocartesianScaffoldCorrectedSecondSharedGlobalIso_eq n k p q).symm

end SerrePositivity.InfinityCategories
