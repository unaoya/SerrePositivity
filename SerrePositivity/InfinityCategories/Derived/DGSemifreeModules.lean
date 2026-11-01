module
public import SerrePositivity.InfinityCategories.Derived.DGFullSubcategoryNerve
public import SerrePositivity.InfinityCategories.Derived.DGModuleNerveHomotopyEquivalence
public import SerrePositivity.DifferentialGraded.Derived.SemifreeProjective
public import SerrePositivity.DifferentialGraded.Derived.ProjectiveHomotopyHom
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
/-- 全次数 Hom end を持つ右 dg 加群の半自由条件。 -/
def dgModuleSemifreeProperty (M : RightModule R D) : Prop :=
  moduleSemifree R D (ForgetEnrichment.of (Complex R) M)
/-- 実半自由 filtration を持つ右 dg 加群の充満 dg 部分圏。 -/
abbrev SemifreeDGModules := DGFullSubcategory (RightModule R D) (dgModuleSemifreeProperty R D)
/-- 任意の小さい dg 圏上の半自由加群による導来 ∞ 圏の模型。 -/
abbrev dgModuleDerivedInfinityCategory := dgNerve R (SemifreeDGModules R D)
/-- 半自由加群の実包含の nerve は、全写像空間で充満忠実。 -/
lemma dgSemifreeModulesInclusion_isFullyFaithful : IsFullyFaithful
    (dgNerve.map (dgFullSubcategoryInclusion R (RightModule R D) (dgModuleSemifreeProperty R D))) :=
  dgFullSubcategoryInclusionNerve_isFullyFaithful R (RightModule R D) _
/-- 半自由加群は、各評価ではなく全 Hom end の意味で homotopically projective。 -/
lemma dgSemifreeModule_isProjective (M : SemifreeDGModules R D) :
    moduleHomotopicallyProjective R D (ForgetEnrichment.of (Complex R) M.val) :=
  moduleSemifree_homotopicallyProjective R D M.property
/-- 半自由加群は非有界の相対 K-flat 性を持つ。 -/
lemma dgSemifreeModule_isRelativeKFlat (M : SemifreeDGModules R D) :
    moduleRelativeKFlat R D M.val := moduleSemifree_relativeKFlat R D M.property
/-- 任意の右 dg 加群は、実半自由加群からの次数別全射な準同型を持つ。 -/
lemma dgSemifreeModule_resolution_exists (M : RightModule R D) :
    ∃ (P : SemifreeDGModules R D)
      (π : ForgetEnrichment.of (Complex R) P.val ⟶ ForgetEnrichment.of (Complex R) M),
      moduleDegreewiseSurjective R D π ∧ moduleQuasiIso R D π := by
  obtain ⟨P, π, hP, hs, hq⟩ := exists_semifree_resolution R D
    (ForgetEnrichment.of (Complex R) M)
  exact ⟨⟨ForgetEnrichment.to (Complex R) P, hP⟩, π, hs, hq⟩
/-- 半自由加群間の準同型の実 ambient nerve 辺は可逆。 -/
lemma dgSemifreeModule_quasiIso_isInvertible (M N : SemifreeDGModules R D)
    (f : ForgetEnrichment.of (Complex R) M.val ⟶ ForgetEnrichment.of (Complex R) N.val)
    (hf : moduleQuasiIso R D f) :
    IsInvertibleEdge (X := dgModuleNerve R D) (dgModuleEdge R D f).toTruncated := by
  have := dgModuleEdge_isIso_of_homotopy R D f
    (moduleHomotopicallyProjective_quasiIso_isIso_homotopy R D
      (dgSemifreeModule_isProjective R D M) (dgSemifreeModule_isProjective R D N) f hf)
  exact (edgeToPathHomotopyCategory _).map_isIso
    (Truncated.HomotopyCategory₂.homMk (dgModuleEdge R D f).toTruncated)
end SerrePositivity.InfinityCategories
