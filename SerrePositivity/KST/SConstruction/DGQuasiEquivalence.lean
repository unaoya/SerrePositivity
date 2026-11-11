module
public import SerrePositivity.KST.SConstruction.DGApplication
public import SerrePositivity.KST.SConstruction.MultiRealizationEquivalence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGQuasiEquivalenceNerve

/-! # dg 準同値の全正有限反復 S 実現への接続
概要：前三角 dg 圏の準同値を、完全な逆データと実現後の局所化同型へ送る。
方針：native dg nerve の実同値の逆も完全であることを使う。
規約：一般の Morita 同値は Perf_dg への接続が別途必要。準同値と混同しない。
使われ方：K-4d の Perf 模型比較の基礎。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories SerrePositivity.DifferentialGraded
open SerrePositivity.SimplicialModel
variable (A : Type u) [CommRing A] (D E : Type u)
  [DGCategory A D] [Small.{u} D] [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]
  [DGCategory A E] [Small.{u} E] [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A E]

/-- 指定した厳密 dg 準同値を順方向に保持する、完全な安定入力の同値。 -/
def dgStableQuasiEquivalence (F : DGFunctor A D E) (hF : QuasiEquivalence F) :
    StableModelEquivalence (dgStableModel A D) (dgStableModel A E) := by
  let e := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_map_isQCatEquivalence_of_quasiEquivalence F hF).choose
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor e.inv :=
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence e.symm.isQCatEquivalence
  exact ⟨dgStableMap A D E F,
    ⟨e.inv, preservesCofiberData_of_isExactFunctor e.inv⟩, e.homInvIso, e.invHomIso⟩

/-- 順方向は元の dg 関手の native nerve を変えない。 -/
lemma dgStableQuasiEquivalence_hom (F : DGFunctor A D E) (hF : QuasiEquivalence F) :
    (dgStableQuasiEquivalence A D E F hF).hom = dgStableMap A D E F := rfl

/-- dg 準同値は全正有限反復の元の S 実現を局所化同型へ送る。 -/
lemma dgMultiRealization_map_localized_isIso (F : DGFunctor A D E)
    (hF : QuasiEquivalence F) (r : ℕ) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      ((multiRealizationFunctor (r + 1)).map (dgStableMap A D E F))) :=
  multiRealization_map_localized_isIso_of_equivalence r (dgStableQuasiEquivalence A D E F hF)

end SerrePositivity.KST.SConstruction
