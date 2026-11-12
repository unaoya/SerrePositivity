module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorVerdier
public import SerrePositivity.KST.SConstruction.DGKUniverseMorita

/-!
概要：元 gluing の cell 増大と resolved 商包含を固定 S の実二辺にする。
方針：同じ分解の厳密 dg 射を ν に送り、増大の Morita 同値の逆で屋根を作る。
規約：native の屋根を S 内の一つの厳密 dg 射と取り違えない。
使われ方：K-10 の新しい商経路と native Verdier 列の照合。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories LocalizingInvariants
variable (R : Type u) [CommRing R] (d : DGOdotInput R)

/-- 概要：元 gluing の同じ cell 平坦源を固定 S に置く。
方針：全 Hom を保つ対象宇宙持ち上げ。規約：分解を選び直さない。
使われ方：resolved 射影の屋根の中央入力。 -/
def dgOdotMilnorCellInput : PerfDGInput.{u, u + 1} R :=
  dgKUniverseInput.{u, u + 1, u + 1} R
    (DGCategoryCellResolution.Source R (DGOdotGluing R d))

/-- 概要：同じ cell 平坦源の対角像商を固定 S に置く。
方針：D2 と同じ null 対象集合を使う。規約：未分解商は使わない。
使われ方：新しい ν 屋根の終点。 -/
def dgOdotMilnorResolvedInput : PerfDGInput.{u, u + 1} R :=
  dgKUniverseInput.{u, u + 1, u + 1} R
    (DGQuotient.QuotientObject (DGCategoryCellResolution.Source R (DGOdotGluing R d))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects R (DGOdotGluing R d)
        (dgQuotientImage R (dgOdotQuotientInput R d).diagonal)))

/-- 概要：同じ cell 増大を S の全 Hom を持つ実辺へ移す。
方針：元の厳密 dg 増大を持ち上げる。規約：逆の厳密 dg 射は仮定しない。
使われ方：resolved 屋根の左辺。 -/
def dgOdotMilnorAugmentationInputMap :
    dgOdotMilnorCellInput R d ⟶ dgOdotGluingInput R d :=
  ULift.up (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor.{u, u + 1, u + 1, u + 1, u + 1}
    (DGCategoryCellResolution.augmentation R (DGOdotGluing R d)))

/-- 概要：同じ実商包含を固定 S の辺へ移す。
方針：D2 の resolved 商と同じ strict 包含を使う。規約：旧射影へ戻さない。
使われ方：resolved 屋根の右辺。 -/
def dgOdotMilnorCellProjectionInputMap :
    dgOdotMilnorCellInput R d ⟶ dgOdotMilnorResolvedInput R d :=
  ULift.up (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor.{u, u + 1, u + 1, u + 1, u + 1}
    (DGQuotient.inclusion R (DGCategoryCellResolution.Source R (DGOdotGluing R d))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects R (DGOdotGluing R d)
        (dgQuotientImage R (dgOdotQuotientInput R d).diagonal))))

/-- 概要：同じ増大の完全な ν 像。方針：固定界面を使用する。
規約：安定値の型を明示する。使われ方：同じ屋根の左辺。 -/
abbrev dgOdotMilnorAugmentationExactMap : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap
    (dgKInputStableValue R (dgOdotMilnorCellInput R d))
    (dgKInputStableValue R (dgOdotGluingInput R d)) :=
  dgKInputNuMap R (dgOdotMilnorAugmentationInputMap R d)

/-- 概要：同じ商包含の完全な ν 像。方針：固定界面を使用する。
規約：安定値の型を明示する。使われ方：同じ屋根の右辺。 -/
abbrev dgOdotMilnorCellProjectionExactMap : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap
    (dgKInputStableValue R (dgOdotMilnorCellInput R d))
    (dgKInputStableValue R (dgOdotMilnorResolvedInput R d)) :=
  dgKInputNuMap R (dgOdotMilnorCellProjectionInputMap R d)

/-- 概要：同じ増大の固定 ν 像は同値。
方針：実準同値を Perf へ延長し、宇宙持ち上げの Morita 保存を使う。
規約：Milnor 仮定は不要。使われ方：ν 上での同じ屋根の構成。 -/
lemma dgOdotMilnorAugmentationNu_isQCatEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap
      (dgKInputStableValue R (dgOdotMilnorCellInput R d))
      (dgKInputStableValue R (dgOdotGluingInput R d)) from
      dgKInputNuMap R (dgOdotMilnorAugmentationInputMap R d)).hom := by
  letI : (quasiEquivalencePerfectExtension R
      (DGCategoryCellResolution.Source R (DGOdotGluing R d)) (DGOdotGluing R d)
      (DGCategoryCellResolution.augmentation R (DGOdotGluing R d))).IsEquivalence :=
    (quasiEquivalencePerfectEquivalence R
    (DGCategoryCellResolution.Source R (DGOdotGluing R d)) (DGOdotGluing R d)
    (DGCategoryCellResolution.augmentation R (DGOdotGluing R d))
    (DGCategoryCellResolution.augmentation_quasiEquivalence R (DGOdotGluing R d))).isEquivalence_functor
  letI : (quasiEquivalencePerfectExtension R (dgOdotMilnorCellInput R d)
      (dgOdotGluingInput R d) (dgOdotMilnorAugmentationInputMap R d).down).IsEquivalence :=
    dgKUniverseLiftFunctor_isMorita R
    (DGCategoryCellResolution.Source R (DGOdotGluing R d)) (DGOdotGluing R d)
    (DGCategoryCellResolution.augmentation R (DGOdotGluing R d))
  rw [dgKInputNuMap_eq]
  exact presentedPerfectDGMoritaAction_isQCatEquivalence R _ _
    (dgOdotMilnorAugmentationInputMap R d).down

/-- 概要：ν に送った同じ増大の順方向を固定した同値。
方針：構成済みの同値証拠を束ねる。規約：元の増大辺を保持する。
使われ方：resolved 屋根の ν 像。 -/
def dgOdotMilnorAugmentationNuEquivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
    (dgKInputStableValue R (dgOdotMilnorCellInput R d)).obj
    (dgKInputStableValue R (dgOdotGluingInput R d)).obj :=
  (dgOdotMilnorAugmentationNu_isQCatEquivalence R d).choose

/-- 概要：元 ν(gluing) から resolved 商の ν 値への同じ二辺の屋根。
方針：ν 増大の逆と ν 商包含を合成する。規約：native 商性はまだ転送しない。
使われ方：固定 ν の新しい商経路の具体的な完全射。 -/
def dgOdotMilnorResolvedProjectionNu : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap
    (dgKInputStableValue R (dgOdotGluingInput R d))
    (dgKInputStableValue R (dgOdotMilnorResolvedInput R d)) where
  hom := (dgOdotMilnorAugmentationNuEquivalence R d).inv ≫
    (dgOdotMilnorCellProjectionExactMap R d).hom
  isExact := by
    letI : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (dgOdotMilnorAugmentationNuEquivalence R d).inv :=
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence
      (dgOdotMilnorAugmentationNuEquivalence R d).symm.isQCatEquivalence
    letI := (dgOdotMilnorCellProjectionExactMap R d).isExact
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isExactFunctor_comp _ _

/-- 概要：ν 屋根は cell 増大上で同じ実商包含を回収する。
方針：同じ同値の指定単位二胞体を後合成する。
規約：厳密等号を要求しない。使われ方：resolved 射影との比較境界。 -/
def dgOdotMilnorResolvedProjectionNu_roof : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((dgOdotMilnorAugmentationExactMap R d).hom ≫
      (dgOdotMilnorResolvedProjectionNu R d).hom)
    (dgOdotMilnorCellProjectionExactMap R d).hom := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((dgOdotMilnorAugmentationNuEquivalence R d).hom ≫
      ((dgOdotMilnorAugmentationNuEquivalence R d).inv ≫
        (dgOdotMilnorCellProjectionExactMap R d).hom)) _
  rw [← Category.assoc]
  simpa only [Category.id_comp] using
    ((dgOdotMilnorAugmentationNuEquivalence R d).homInvIso.postcomp
      (dgOdotMilnorCellProjectionExactMap R d).hom)

end SerrePositivity.KST.SConstruction
