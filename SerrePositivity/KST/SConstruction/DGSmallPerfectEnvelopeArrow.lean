module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.FunctorHomTypedWhiskerAlgebra
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.SimplicialFunctors.FunctorHomIsIsoTransport
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.SimplicialFunctors.FunctorHomWhiskering
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGStrictNerveWhiskerHom
public import SerrePositivity.KST.SConstruction.DGSmallPerfectEnvelopeFunctorLift
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGStrictNatTransTransport
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGStrictNatTransNerveHomTransport

/-!
概要：元 Perf 比較射を二実像小包絡へ制限し、元の全 native 射を回収する。
方針：同じ全 Hom の充満部分圏で元の厳密変換を保持する。
規約：対象別比較で全変換を代用しない。使われ方：実中央比較の小基底表示。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (J : Type w) (X : J → PerfectDGModule R D) (P : Type (max (u + 1) v)) [DGCategory R P]
  (F G : DGFunctor R P (PerfectDGModule R D))
  (i j : P → J) (hF : ∀ a, X (i a) = F.obj a) (hG : ∀ a, X (j a) = G.obj a)
  (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G)
local notation "L" => dgSmallPerfectEnvelopeFunctorLift R D J X F i hF
local notation "M" => dgSmallPerfectEnvelopeFunctorLift R D J X G j hG
local notation "I" => dgSmallPerfectEnvelopeInclusion R D J X

/-- 概要：同じ元の厳密 dg 比較を元二像小模型内に保持する。
方針：全 Hom と元の閉零成分をそのまま使う。
規約：元射を共役で置換しない。使われ方：小基底の native 全射。 -/
def dgSmallPerfectEnvelopeStrictNatTrans : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans (L) (M) where
  app x := η.app x
  naturality f := η.naturality f

/-- 概要：同じ小模型内比較の包含像は元の全厳密比較そのもの。
方針：両関手の全 dg 回収と同じ全閉零成分を照合する。
規約：全変換の同定。使われ方：同じ native 比較射の厳密回収。 -/
lemma dgSmallPerfectEnvelopeStrictNatTrans_inclusion :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp
      (dgSmallPerfectEnvelopeStrictNatTrans R D J X P F G i j hF hG η) (I)) η := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTrans_heq_of_val _ η
    (dgSmallPerfectEnvelopeFunctorLift_inclusion R D J X F i hF)
    (dgSmallPerfectEnvelopeFunctorLift_inclusion R D J X G j hG)
  intro x
  rfl

/-- 概要：同じ二像小模型内の元比較を全 native 射にする。
方針：元厳密変換の同じ nerve 作用を使用する。
規約：元の全比較を保持。使われ方：包絡値同値による全射の移送。 -/
def dgSmallPerfectEnvelopeNerveArrow : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (L)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (M)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R P (DGSmallPerfectEnvelope R D J X)
    (dgSmallPerfectEnvelopeStrictNatTrans R D J X P F G i j hF hG η)

/-- 概要：小模型の同じ全 native 射の包含像は元 Perf 全射。
方針：元全変換の包含同定と nerve の後合成整合性を使う。
規約：頂点成分だけで代用しない。使われ方：元の比較射の同一性。 -/
lemma dgSmallPerfectEnvelopeNerveArrow_inclusion :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (L)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (M)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (I))
      (dgSmallPerfectEnvelopeNerveArrow R D J X P F G i j hF hG η))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R P (PerfectDGModule R D) η) := by
  have a := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom_postcomp_heq R P (DGSmallPerfectEnvelope R D J X)
    (PerfectDGModule R D) (dgSmallPerfectEnvelopeStrictNatTrans R D J X P F G i j hF hG η) (I)
  have b := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom_heq R P (PerfectDGModule R D)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp (dgSmallPerfectEnvelopeStrictNatTrans R D J X P F G i j hF hG η) (I)) η
    (dgSmallPerfectEnvelopeFunctorLift_inclusion R D J X F i hF)
    (dgSmallPerfectEnvelopeFunctorLift_inclusion R D J X G j hG)
    (dgSmallPerfectEnvelopeStrictNatTrans_inclusion R D J X P F G i j hF hG η)
  exact a.symm.trans b

/-- 概要：同じ小模型全射の任意の元終域評価後の像も元 Perf 全射を回収する。
方針：全包含回収を元評価で後合成し、同じ二段作用を照合する。
規約：元比較射を保持。使われ方：同じ固定 ν 値への全射の移送。 -/
lemma dgSmallPerfectEnvelopeNerveArrow_evaluation
    {Z : SSet.{max (u + 1) v}} (k : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (PerfectDGModule R D) ⟶ Z) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (L)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (M)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (I) ≫ k)
      (dgSmallPerfectEnvelopeNerveArrow R D J X P F G i j hF hG η))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map G) k
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R P (PerfectDGModule R D) η)) := by
  let a := dgSmallPerfectEnvelopeNerveArrow R D J X P F G i j hF hG η
  let b := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R P (PerfectDGModule R D) η
  have h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (L) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (I) = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, dgSmallPerfectEnvelopeFunctorLift_inclusion]
  have h₂ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (M) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (I) = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map G := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, dgSmallPerfectEnvelopeFunctorLift_inclusion]
  have h₃ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp_heq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (I)) a) b h₁ h₂
    (dgSmallPerfectEnvelopeNerveArrow_inclusion R D J X P F G i j hF hG η) k
  exact (heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp_postcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (L)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (M))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (I)) k a).symm).trans h₃

end SerrePositivity.KST.SConstruction
