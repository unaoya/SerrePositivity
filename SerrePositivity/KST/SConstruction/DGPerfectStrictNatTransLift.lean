module
public import SerrePositivity.KST.SConstruction.DGPerfectModuleUnderlyingInclusion
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGStrictNatTransTransport
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGStrictNatTransWhisker
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGStrictNerveWhiskerHom
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGStrictNatTransNerveHomTransport
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.FunctorHomTypedWhiskerAlgebra

/-!
概要：同じ実 Perf 全族間の全厳密自然変換を元加群値変換から保持する。
方針：指定包含等号で端点を移し、元全 Hom と自然性を制限する。
規約：元 cycle・全自然性を変更しない。
使われ方：元実逆回転の包含を同じ Perf 内で持ち上げる。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E] [Small.{u} E]
  {P : Type (max (u + 1) v)} [DGCategory R P]
  (F G : DGFunctor R P (PerfectDGModule R E))
  {F' G' : DGFunctor R P (RightModule R E)}
  (hF : dgPerfectModuleUnderlying R E F = F')
  (hG : dgPerfectModuleUnderlying R E G = G') (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F' G')

/-- 概要：元加群値の全変換を同じ実 Perf 全族間へ制限する。
方針：元指定包含で端点を移した同じ cycle を使う。
規約：全自然性を保持。使われ方：同じ実 Perf 包含辺。 -/
def dgPerfectStrictNatTransLift : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G := by
  let t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans (dgPerfectModuleUnderlying R E F) (dgPerfectModuleUnderlying R E G) := by
    rw [hF, hG]
    exact η
  exact { app := t.app, naturality := t.naturality }

/-- 概要：同じ Perf 持ち上げは包含後に元全厳密変換を回収する。
方針：元端点等号を消去し、元全 cycle を比較する。
規約：全厳密変換の型付き一致。使われ方：元 native 包含辺の反映。 -/
lemma dgPerfectStrictNatTransLift_inclusion :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp (dgPerfectStrictNatTransLift R E F G hF hG η)
      (perfectDGModuleInclusion R E Set.univ)) η := by
  subst F' G'
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTrans_heq_of_val _ η
    (dgPerfectModuleUnderlying_inclusion R E F).symm
    (dgPerfectModuleUnderlying_inclusion R E G).symm
  intro x
  rfl
/-- 概要：元 Perf 制限の native 全射は元包含後に元全加群射を回収する。
方針：抽象的な元全変換の回収と native 後合成則を使う。
規約：元全射の型付き一致。使われ方：具体的二段包含の同じ全境界。 -/
lemma dgPerfectStrictNatTransLift_nerve_inclusion :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map G)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (perfectDGModuleInclusion R E Set.univ))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R P (PerfectDGModule R E)
        (dgPerfectStrictNatTransLift R E F G hF hG η)))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R P (RightModule R E) η) := by
  have hp := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom_postcomp_heq R P
    (PerfectDGModule R E) (RightModule R E)
    (dgPerfectStrictNatTransLift R E F G hF hG η) (perfectDGModuleInclusion R E Set.univ)
  have hs := (dgPerfectModuleUnderlying_inclusion R E F).symm.trans hF
  have ht := (dgPerfectModuleUnderlying_inclusion R E G).symm.trans hG
  have hn := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom_heq R P (RightModule R E)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp (dgPerfectStrictNatTransLift R E F G hF hG η)
      (perfectDGModuleInclusion R E Set.univ)) η hs ht
    (dgPerfectStrictNatTransLift_inclusion R E F G hF hG η)
  exact hp.symm.trans hn
end SerrePositivity.KST.SConstruction
