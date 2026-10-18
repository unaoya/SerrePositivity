module

public import SerrePositivity.InfinityCategories.HomotopyLimits.ConeFamilyApex
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoherentConeSectionSpace

/-!
概要：coslice の切断空間から内部 Hom の固定頂点の錐の模型への比較射。
方針：相対評価を coslice の普遍性で展開し、join と直積の比較の後で curry する。
規約：高次のパラメータを含む実際の単体集合の射を構成する。
使われ方：Kerodon 4.6.6.8、7.4.1.6、7.5.4.6 の二つの錐の模型の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 概要：切断の普遍族を錐の形とパラメータの直積上に展開する。
方針：join の右因子へパラメータを移し、相対評価を coslice から uncurry する。
規約：頂点 x と図式 p は全次数で固定する。
使われ方：Kerodon 7.4.1.6、7.5.4.6 の切断側の比較の uncurry。 -/
noncomputable def sectionConeFamilyUncurry {K X : SSet.{u}} (p : K ⟶ X)
    (x : X _⦋0⦌) : join (Δ[0] : SSet.{u}) K ⊗ coherentConeSectionSpace p x ⟶ X :=
  joinTensorRight Δ[0] K (coherentConeSectionSpace p x) ≫
    sliceUnderUncurry (relativeFunctorUncurry (𝟙 (coherentConeSectionSpace p x)))

/-- 概要：切断の普遍錐の右端は元の図式の定値族である。
方針：join の右包含上の比較と coslice の射影と相対評価の式を順に使う。
規約：固定条件は直積の第一射影を通る厳密な等式。
使われ方：Kerodon 4.6.6.8、7.5.4.6 の錐の fiber への持ち上げ。 -/
lemma sectionConeFamilyUncurry_fixed {K X : SSet.{u}} (p : K ⟶ X)
    (x : X _⦋0⦌) :
    (joinInr Δ[0] K ▷ coherentConeSectionSpace p x) ≫ sectionConeFamilyUncurry p x =
      fst K (coherentConeSectionSpace p x) ≫ p := by
  unfold sectionConeFamilyUncurry
  rw [← Category.assoc, joinTensorRight_inr, sliceUnderUncurry_projection]
  exact relativeFunctorUncurry_projection _

/-- 概要：切断の普遍錐を curry すると図式を固定した内部 Hom の錐になる。
方針：図式への制限を uncurry し、右端の固定条件を使う。
規約：元の X の充填性は要求しない。
使われ方：Kerodon 4.6.6.8、7.5.4.6 の共通模型への射の準備。 -/
lemma sectionConeFamilyUncurry_curry_fixed {K X : SSet.{u}} (p : K ⟶ X)
    (x : X _⦋0⦌) :
    curry (sectionConeFamilyUncurry p x) ≫ coneRestriction K X =
      SSet.const (functorVertex p) := by
  apply uncurry_injective
  rw [coneRestriction, uncurry_pre_app, uncurry_curry, sectionConeFamilyUncurry_fixed,
    uncurry_const_functorVertex]

/-- 概要：切断空間は内部 Hom で表した錐の空間へ標準的に写る。
方針：普遍錐を curry し、図式を固定する fiber へ持ち上げる。
規約：この段階では頂点 x の fiber への制限は行わない。
使われ方：Kerodon 4.6.6.8、7.4.1.6 の錐の模型間の実際の射。 -/
noncomputable def sectionConeFamilyMap {K X : SSet.{u}} (p : K ⟶ X)
    (x : X _⦋0⦌) : coherentConeSectionSpace p x ⟶ coneFamily p :=
  vertexFiberLift (coneRestriction K X) (functorVertex p)
    (curry (sectionConeFamilyUncurry p x)) (sectionConeFamilyUncurry_curry_fixed p x)

/-- 概要：切断空間からの比較は錐の頂点を x に固定する。
方針：左包含上の join と直積の比較を計算し、一点の関手空間で評価する。
規約：頂点への射は全次数で定値である。
使われ方：Kerodon 7.4.1.6、7.5.4.6 の固定頂点の共通模型への持ち上げ条件。 -/
lemma sectionConeFamilyMap_apex {K X : SSet.{u}} (p : K ⟶ X) (x : X _⦋0⦌) :
    sectionConeFamilyMap p x ≫ coneFamilyApex p = SSet.const x := by
  have hleft : (joinInl (Δ[0] : SSet.{u}) K ▷ coherentConeSectionSpace p x) ≫
      sectionConeFamilyUncurry p x =
      fst (Δ[0] : SSet.{u}) (coherentConeSectionSpace p x) ≫ SSet.yonedaEquiv.symm x := by
    unfold sectionConeFamilyUncurry
    rw [← Category.assoc, joinTensorRight_inl, Category.assoc, sliceUnderUncurry_fixed]
  change (sectionConeFamilyMap p x ≫
    vertexFiberι (coneRestriction K X) (functorVertex p)) ≫
    (pre (joinInl (Δ[0] : SSet.{u}) K)).app X ≫
    (pointFunctorEvaluationIso X).hom = _
  rw [sectionConeFamilyMap, vertexFiberLift_ι, ← Category.assoc, curry_pre_app, hleft]
  change curry (fst (Δ[0] : SSet.{u}) (coherentConeSectionSpace p x) ≫
    SSet.yonedaEquiv.symm x) ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0) = _
  rw [curry_evaluateFunctorAt_vertex, ← Category.assoc, lift_fst]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  rfl

/-- 概要：coslice の切断空間は内部 Hom の固定頂点の錐へ標準的に写る。
方針：切断から作った錐の頂点の固定条件で fiber へ持ち上げる。
規約：充填性と同値性の仮定を射の定義には置かない。
使われ方：Kerodon 7.4.1.6、7.5.4.6 の二つの模型の共通標的への比較。 -/
noncomputable def sectionFixedApexConeFamilyMap {K X : SSet.{u}} (p : K ⟶ X)
    (x : X _⦋0⦌) : coherentConeSectionSpace p x ⟶ fixedApexConeFamily p x :=
  vertexFiberLift (coneFamilyApex p) x (sectionConeFamilyMap p x)
    (sectionConeFamilyMap_apex p x)

end SerrePositivity.InfinityCategories.HomotopyLimits
