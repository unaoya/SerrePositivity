module

public import SerrePositivity.InfinityCategories.F1.CocartesianTwoSimplexCorrectedGlobalCoherence

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

variable {C : Type u} [Category.{u} C] (k : ULift.{u} (Fin 3) ⥤ C)
  (p q : CocartesianFibrationCategory (nerve C))

/-- 最初の補正成分の共有頂点への指定像を、端点表示だけ揃えた同型。 -/
def cocartesianTwoSimplexCorrectedFirstSharedGlobalIso :
    FunctorIso
      (cocartesianBaseChangeHomNaturalityIso (cocartesianTwoSimplexSharedCell k) p q).sourceMap
      (cocartesianBaseChangeHomNaturalityIso (cocartesianTwoSimplexSharedCell k) p q).targetMap :=
  F2.functorIsoOfEq ((cocartesianTwoSimplexCorrectedFirstGlobalIso k p q).postcomp
    ((cocartesianTwoSimplexLocalTarget k p q).map WalkingCospan.Hom.inl))
    (cocartesianTwoSimplexCorrectedFirstGlobalIso_shared_source k p q)
    (cocartesianTwoSimplexCorrectedFirstGlobalIso_shared_target k p q)

/-- 同じ端点へ揃えた最初の指定像は、元の共有頂点の直接自然性そのもの。 -/
lemma cocartesianTwoSimplexCorrectedFirstSharedGlobalIso_eq :
    cocartesianTwoSimplexCorrectedFirstSharedGlobalIso k p q =
    cocartesianBaseChangeHomNaturalityIso (cocartesianTwoSimplexSharedCell k) p q := by
  exact eq_of_heq ((F2.functorIsoOfEq_heq
    ((cocartesianTwoSimplexCorrectedFirstGlobalIso k p q).postcomp
      ((cocartesianTwoSimplexLocalTarget k p q).map WalkingCospan.Hom.inl))
    (cocartesianTwoSimplexCorrectedFirstGlobalIso_shared_source k p q)
    (cocartesianTwoSimplexCorrectedFirstGlobalIso_shared_target k p q)).trans
    (cocartesianTwoSimplexCorrectedFirstGlobalIso_shared_heq k p q))

/-- 次の補正成分の共有頂点への指定像を、端点表示だけ揃えた同型。 -/
def cocartesianTwoSimplexCorrectedSecondSharedGlobalIso :
    FunctorIso
      (cocartesianBaseChangeHomNaturalityIso (cocartesianTwoSimplexSharedCell k) p q).sourceMap
      (cocartesianBaseChangeHomNaturalityIso (cocartesianTwoSimplexSharedCell k) p q).targetMap :=
  F2.functorIsoOfEq ((cocartesianTwoSimplexCorrectedSecondGlobalIso k p q).postcomp
    ((cocartesianTwoSimplexLocalTarget k p q).map WalkingCospan.Hom.inr))
    (cocartesianTwoSimplexCorrectedSecondGlobalIso_shared_source k p q)
    (cocartesianTwoSimplexCorrectedSecondGlobalIso_shared_target k p q)

/-- 同じ端点へ揃えた次の指定像は、元の共有頂点の直接自然性そのもの。 -/
lemma cocartesianTwoSimplexCorrectedSecondSharedGlobalIso_eq :
    cocartesianTwoSimplexCorrectedSecondSharedGlobalIso k p q =
    cocartesianBaseChangeHomNaturalityIso (cocartesianTwoSimplexSharedCell k) p q := by
  exact eq_of_heq ((F2.functorIsoOfEq_heq
    ((cocartesianTwoSimplexCorrectedSecondGlobalIso k p q).postcomp
      ((cocartesianTwoSimplexLocalTarget k p q).map WalkingCospan.Hom.inr))
    (cocartesianTwoSimplexCorrectedSecondGlobalIso_shared_source k p q)
    (cocartesianTwoSimplexCorrectedSecondGlobalIso_shared_target k p q)).trans
    (cocartesianTwoSimplexCorrectedSecondGlobalIso_shared_heq k p q))

/-- 元の全 Hom 上で、二つの補正成分の共有頂点への指定像は厳密に一致する。 -/
lemma cocartesianTwoSimplexCorrectedSharedGlobalIso_coherence :
    cocartesianTwoSimplexCorrectedFirstSharedGlobalIso k p q =
      cocartesianTwoSimplexCorrectedSecondSharedGlobalIso k p q :=
  (cocartesianTwoSimplexCorrectedFirstSharedGlobalIso_eq k p q).trans
    (cocartesianTwoSimplexCorrectedSecondSharedGlobalIso_eq k p q).symm

end SerrePositivity.InfinityCategories
