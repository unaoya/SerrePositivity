module
public import SerrePositivity.KST.SConstruction.DGPerfectComparisonInverseRotationPerfectRealized
public import SerrePositivity.KST.SConstruction.DGIdentityInverseRotationPerfectInclusion
public import SerrePositivity.KST.SConstruction.DGPerfectComparisonInverseRotationRealizedBoundary

/-!
概要：元二段実逆回転の実包含を同じ二段 Perf 全族間に保持する。
方針：同じ元右軸・実評価を二段とも使用し、元包含の全厳密変換を制限する。
規約：元の実包含・元対象像・全自然性を保持する。
使われ方：同じ resolved 射影の Perf 全比較と固定 ν の指定上面の接続。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories MonoidalCategory
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E] [Small.{u} E]
  {P : Type (max (u + 1) v)} [DGCategory R P] [Small.{u} P]
  (F G : DGFunctor R P (PerfectDGModule R E))
  (τ : DGFunctorParamTrans R P (PerfectDGModule R E) (𝟙_ (Complex R)) F G)
local notation "T" => DGPerfectComparisonBase R E F G
local notation "family" => dgPerfectComparisonFamily R E F G
local notation "J" => dgSmallPerfectEnvelopeInclusion R E (P ⊕ P) (family)
local notation "V" => dgPerfectRealization R (T) E (J)
local notation "F0" => dgPerfectComparisonFirst R E F G
local notation "G0" => dgPerfectComparisonSecond R E F G
local notation "a" => dgPerfectComparisonMap R E F G τ
local notation "h" => dgPerfectComparisonMap_hom_naturality R E F G τ
local notation "H" => dgPerfectComparisonHomGluingFunctor R E F G τ
local notation "Q" => dgIdentityInverseRotationRealizedConeFamily R (T)

local notation "QP" => dgIdentityInverseRotationPerfectRealizedConeFamily R (T)
local notation "VP" => dgPerfectRealizationPerfect R (T) E (J)
local notation "i" => perfectDGModuleInclusion R E Set.univ

local notation "TP" => dgIdentityInverseRotationPerfectTargetFamily R (T)
local notation "TF" => dgIdentityHomGluingInverseRotationTargetFamily R (T) (F0) (G0) (a) (h)
local notation "RF" => dgPerfectComparisonInverseRotationPerfectRealizedFamily R E F G τ
local notation "IR" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp
  (dgIdentityHomGluingInverseRotationRealizedInr R (T) (F0) (G0) (a) (h)) (V)

/-- 概要：元実包含の始域を同じ二段実 Perf 全族として保持する。
方針：元右軸の Perf 全族を元入力で制限して同じ第二段評価へ送る。
規約：同じ元実像を保持。使われ方：元 Perf 包含の始域。 -/
def dgPerfectComparisonInverseRotationPerfectTargetFamily :
    DGFunctor R P (PerfectDGModule R E) := ((H).comp (TP)).comp (VP)

/-- 概要：元二段 Perf 右軸は包含後に元二段全評価の右軸そのもの。
方針：二段の同じ包含回収を使用する。
規約：全 dg 関手の等号。使われ方：元包含の Perf 制限。 -/
lemma dgPerfectComparisonInverseRotationPerfectTargetFamily_underlying :
    dgPerfectModuleUnderlying R E
      (dgPerfectComparisonInverseRotationPerfectTargetFamily R E F G τ) = (TF).comp (V) := by
  change dgPerfectModuleUnderlying R E (((H).comp (TP)).comp (VP)) = (TF).comp (V)
  rw [dgPerfectRealizationPerfect_underlying, ← dgPerfectModuleUnderlying_comp,
    dgIdentityInverseRotationPerfectTargetFamily_underlying]
  rfl

/-- 概要：同じ元実包含の二段 Perf 全族間の全厳密変換。
方針：同じ元全変換を証明済み二段包含等号に沿って制限する。
規約：全自然性と元 cycle を保持。使われ方：固定 ν へ送る元包含辺。 -/
def dgPerfectComparisonInverseRotationPerfectInr :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans (dgPerfectComparisonInverseRotationPerfectTargetFamily R E F G τ) (RF) :=
  dgPerfectStrictNatTransLift R E
    (dgPerfectComparisonInverseRotationPerfectTargetFamily R E F G τ) (RF)
    (dgPerfectComparisonInverseRotationPerfectTargetFamily_underlying R E F G τ)
    (dgPerfectComparisonInverseRotationPerfectRealizedFamily_underlying R E F G τ) (IR)

/-- 概要：元二段 Perf 包含は全加群への包含後に元二段全実包含を回収する。
方針：同じ元全変換の制限回収を使用する。
規約：元全厳密変換の型付き一致。使われ方：元全境界を同じ Perf 比較へ反映。 -/
lemma dgPerfectComparisonInverseRotationPerfectInr_inclusion :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp
      (dgPerfectComparisonInverseRotationPerfectInr R E F G τ) (i)) (IR) :=
  dgPerfectStrictNatTransLift_inclusion R E
    (dgPerfectComparisonInverseRotationPerfectTargetFamily R E F G τ) (RF)
    (dgPerfectComparisonInverseRotationPerfectTargetFamily_underlying R E F G τ)
    (dgPerfectComparisonInverseRotationPerfectRealizedFamily_underlying R E F G τ) (IR)
/-- 概要：元二段 Perf 包含の native 全射は包含後に元二段実包含を回収する。
方針：全厳密変換の回収と既存の native 後合成則を組み合わせる。
規約：同じ全関手射の型付き一致。使われ方：同じ固定 ν 全比較への包含境界。 -/
lemma dgPerfectComparisonInverseRotationPerfectInr_nerve_inclusion :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgPerfectComparisonInverseRotationPerfectTargetFamily R E F G τ))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (RF)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (i))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R P (PerfectDGModule R E)
        (dgPerfectComparisonInverseRotationPerfectInr R E F G τ)))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R P (RightModule R E) (IR)) :=
  dgPerfectStrictNatTransLift_nerve_inclusion R E
    (dgPerfectComparisonInverseRotationPerfectTargetFamily R E F G τ) (RF)
    (dgPerfectComparisonInverseRotationPerfectTargetFamily_underlying R E F G τ)
    (dgPerfectComparisonInverseRotationPerfectRealizedFamily_underlying R E F G τ) (IR)
end SerrePositivity.KST.SConstruction
