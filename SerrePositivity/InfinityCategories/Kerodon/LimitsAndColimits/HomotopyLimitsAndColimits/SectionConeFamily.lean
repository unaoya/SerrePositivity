module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ConeFamilyApex
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.CoherentConeSectionSpace

/-!
概要：coslice の切断空間から内部 Hom の固定頂点の錐の模型への比較射。
方針：相対評価を coslice の普遍性で展開し、join と直積の比較の後で curry する。
規約：高次のパラメータを含む実際の単体集合の射を構成する。
使われ方：Kerodon 4.6.6.8（Tag 04J5）、7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の二つの錐の模型の比較。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits

/-- 概要：切断の普遍族を錐の形とパラメータの直積上に展開する。
方針：join の右因子へパラメータを移し、相対評価を coslice から uncurry する。
規約：頂点 x と図式 p は全次数で固定する。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の切断側の比較の uncurry。 -/
noncomputable def sectionConeFamilyUncurry {K X : SSet.{u}} (p : K ⟶ X)
    (x : X _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) K ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeSectionSpace p x ⟶ X :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinTensorRight Δ[0] K (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeSectionSpace p x) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeSectionSpace p x)))

/-- 概要：切断の普遍錐の右端は元の図式の定値族である。
方針：join の右包含上の比較と coslice の射影と相対評価の式を順に使う。
規約：固定条件は直積の第一射影を通る厳密な等式。
使われ方：Kerodon 4.6.6.8（Tag 04J5）、7.5.4.6（Tag 03BB） の錐の fiber への持ち上げ。 -/
lemma sectionConeFamilyUncurry_fixed {K X : SSet.{u}} (p : K ⟶ X)
    (x : X _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] K ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeSectionSpace p x) ≫ sectionConeFamilyUncurry p x =
      fst K (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeSectionSpace p x) ≫ p := by
  unfold sectionConeFamilyUncurry
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinTensorRight_inr, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceUnderUncurry_projection]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_projection _

/-- 概要：切断の普遍錐を curry すると図式を固定した内部 Hom の錐になる。
方針：図式への制限を uncurry し、右端の固定条件を使う。
規約：元の X の充填性は要求しない。
使われ方：Kerodon 4.6.6.8（Tag 04J5）、7.5.4.6（Tag 03BB） の共通模型への射の準備。 -/
lemma sectionConeFamilyUncurry_curry_fixed {K X : SSet.{u}} (p : K ⟶ X)
    (x : X _⦋0⦌) :
    curry (sectionConeFamilyUncurry p x) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction K X =
      SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p) := by
  apply uncurry_injective
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction, uncurry_pre_app, uncurry_curry, sectionConeFamilyUncurry_fixed,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex]

/-- 概要：切断空間は内部 Hom で表した錐の空間へ標準的に写る。
方針：普遍錐を curry し、図式を固定する fiber へ持ち上げる。
規約：この段階では頂点 x の fiber への制限は行わない。
使われ方：Kerodon 4.6.6.8（Tag 04J5）、7.4.1.6（Tag 05QS） の錐の模型間の実際の射。 -/
noncomputable def sectionConeFamilyMap {K X : SSet.{u}} (p : K ⟶ X)
    (x : X _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeSectionSpace p x ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneFamily p :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction K X) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p)
    (curry (sectionConeFamilyUncurry p x)) (sectionConeFamilyUncurry_curry_fixed p x)

/-- 概要：切断空間からの比較は錐の頂点を x に固定する。
方針：左包含上の join と直積の比較を計算し、一点の関手空間で評価する。
規約：頂点への射は全次数で定値である。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の固定頂点の共通模型への持ち上げ条件。 -/
lemma sectionConeFamilyMap_apex {K X : SSet.{u}} (p : K ⟶ X) (x : X _⦋0⦌) :
    sectionConeFamilyMap p x ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneFamilyApex p = SSet.const x := by
  have hleft : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) K ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeSectionSpace p x) ≫
      sectionConeFamilyUncurry p x =
      fst (Δ[0] : SSet.{u}) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeSectionSpace p x) ≫ SSet.yonedaEquiv.symm x := by
    unfold sectionConeFamilyUncurry
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinTensorRight_inl, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_fixed]
  change (sectionConeFamilyMap p x ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction K X) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p)) ≫
    (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) K)).app X ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso X).hom = _
  rw [sectionConeFamilyMap, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι, ← Category.assoc, curry_pre_app, hleft]
  change curry (fst (Δ[0] : SSet.{u}) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeSectionSpace p x) ≫
    SSet.yonedaEquiv.symm x) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.curry_evaluateFunctorAt_vertex, ← Category.assoc, lift_fst]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  rfl

/-- 概要：coslice の切断空間は内部 Hom の固定頂点の錐へ標準的に写る。
方針：切断から作った錐の頂点の固定条件で fiber へ持ち上げる。
規約：充填性と同値性の仮定を射の定義には置かない。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の二つの模型の共通標的への比較。 -/
noncomputable def sectionFixedApexConeFamilyMap {K X : SSet.{u}} (p : K ⟶ X)
    (x : X _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeSectionSpace p x ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedApexConeFamily p x :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneFamilyApex p) x (sectionConeFamilyMap p x)
    (sectionConeFamilyMap_apex p x)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
