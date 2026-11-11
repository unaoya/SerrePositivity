module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFullSubcategoryNerve
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleNerveHomotopyEquivalence
public import SerrePositivity.DifferentialGraded.Derived.Basic
public import SerrePositivity.DifferentialGraded.Derived.Projective
public import SerrePositivity.DifferentialGraded.Tensor.Graded
/-!
概要：任意の小さい dg 圏上の半自由加群の実 dg nerve と分解を定義する。
方針：全次数 Hom end と実半自由 filtration をそのまま使う。
規約：基礎可換環と作用する dg 圏を分離。一対象の場合は非可換 dg 代数の加群を扱う。
使われ方：β5 の D(A)、相対 tensor・Hom の模型。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
/-- 全次数 Hom end を持つ右 dg 加群の半自由条件。 -/
def dgModuleSemifreeProperty (M : _root_.SerrePositivity.DifferentialGraded.RightModule R D) : Prop :=
  _root_.SerrePositivity.DifferentialGraded.moduleSemifree R D (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) M)
/-- 実半自由 filtration を持つ右 dg 加群の充満 dg 部分圏。 -/
abbrev SemifreeDGModules := _root_.SerrePositivity.DifferentialGraded.DGFullSubcategory (_root_.SerrePositivity.DifferentialGraded.RightModule R D) (dgModuleSemifreeProperty R D)
/-- 任意の小さい dg 圏上の半自由加群による導来 ∞ 圏の模型。 -/
abbrev dgModuleDerivedInfinityCategory := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (SemifreeDGModules R D)
/-- 半自由加群の実包含の nerve は、全写像空間で充満忠実。 -/
lemma dgSemifreeModulesInclusion_isFullyFaithful : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion R (RightModule R D) (dgModuleSemifreeProperty R D))) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullSubcategoryInclusionNerve_isFullyFaithful R (RightModule R D) _
/-- 半自由加群は、各評価ではなく全 Hom end の意味で homotopically projective。 -/
lemma dgSemifreeModule_isProjective (M : SemifreeDGModules R D) :
    _root_.SerrePositivity.DifferentialGraded.moduleHomotopicallyProjective R D (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) M.val) :=
  _root_.SerrePositivity.DifferentialGraded.moduleSemifree_homotopicallyProjective R D M.property
/-- 半自由加群は非有界の相対 K-flat 性を持つ。 -/
lemma dgSemifreeModule_isRelativeKFlat (M : SemifreeDGModules R D) :
    _root_.SerrePositivity.DifferentialGraded.moduleRelativeKFlat R D M.val := _root_.SerrePositivity.DifferentialGraded.moduleSemifree_relativeKFlat R D M.property
/-- 任意の右 dg 加群は、実半自由加群からの次数別全射な準同型を持つ。 -/
lemma dgSemifreeModule_resolution_exists (M : _root_.SerrePositivity.DifferentialGraded.RightModule R D) :
    ∃ (P : SemifreeDGModules R D)
      (π : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) P.val ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) M),
      _root_.SerrePositivity.DifferentialGraded.moduleDegreewiseSurjective R D π ∧ moduleQuasiIso R D π := by
  obtain ⟨P, π, hP, hs, hq⟩ := _root_.SerrePositivity.DifferentialGraded.exists_semifree_resolution R D
    (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) M)
  exact ⟨⟨ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) P, hP⟩, π, hs, hq⟩
/-- 半自由加群間の準同型の実 ambient nerve 辺は可逆。 -/
lemma dgSemifreeModule_quasiIso_isInvertible (M N : SemifreeDGModules R D)
    (f : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) M.val ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) N.val)
    (hf : _root_.SerrePositivity.DifferentialGraded.moduleQuasiIso R D f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge R D f).toTruncated := by
  have := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge_isIso_of_homotopy R D f
    (_root_.SerrePositivity.DifferentialGraded.moduleHomotopicallyProjective_quasiIso_isIso_homotopy R D
      (dgSemifreeModule_isProjective R D M) (dgSemifreeModule_isProjective R D N) f hf)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeToPathHomotopyCategory _).map_isIso
    (Truncated.HomotopyCategory₂.homMk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge R D f).toTruncated)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
