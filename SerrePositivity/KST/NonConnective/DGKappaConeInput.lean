module

public import SerrePositivity.KST.NonConnective.DGCountableSum
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleResolvedInfinity
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ResolvedDGQuotientVerdierSequence
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.Definition
public import SerrePositivity.DifferentialGraded.Perfect.Compact.Enhancement

/-!
概要：未供給の非可算 κ-compact dg 小模型を、明示の入力として保持する。
方針：実右 dg 加群の選んだ充満小部分圏と、実導来 ∞ 圏内での意味を要求する。
規約：ordinary compact と κ-compact を混同せず、入力の存在を証明済みとしない。
使われ方：D 側の供給をコーディネータが仲介する間の dg cone・懸垂の界面。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]

/-- 元の閉零射圏の型ラベルだけを外す厳密 dg 関手。 -/
def dgConeModuleForget : _root_.SerrePositivity.DifferentialGraded.DGFunctor R (_root_.SerrePositivity.DifferentialGraded.ModuleCategory R D) (_root_.SerrePositivity.DifferentialGraded.RightModule R D) where
  obj := ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R)
  map _ _ := 𝟙 _
  map_id _ := Category.comp_id _
  map_comp _ _ _ := by
    simp only [tensorHom_id, id_whiskerRight, Category.id_comp, Category.comp_id]
    rfl

/-- 元の実加群を、β5 の同じ半自由模型による D(D) に送る実関手。 -/
def dgConeModuleDerived : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (ModuleCategory R D) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (ModuleCategory R D) D (dgConeModuleForget R D)

/-- κ-compact 性を試験する実導来 ∞ 圏での同じ加群頂点。 -/
def dgConeModuleDerivedVertex (M : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D) _⦋0⦌ :=
  (dgConeModuleDerived R D).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex M)

/-- D 側で未供給の、非可算 κ に対する具体的 dg 小模型の明示入力。
存在・κ-compact 閉性・比較をこの構造の存在だけから結論してはならない。 -/
structure DGKappaConeInput (κ : Cardinal.{u}) where
  /-- 非可算性。可算直和の閉性と別に保持する。 -/
  uncountable : Cardinal.aleph0 < κ
  /-- 正則性。 -/
  regular : κ.IsRegular
  /-- 実 dg 加群の選んだ代表系。全同型コピーを含むとは仮定しない。 -/
  objects : Set (_root_.SerrePositivity.DifferentialGraded.ModuleCategory R D)
  /-- 選んだ代表系自体の u-small 性。 -/
  small : Small.{u} {M : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D // objects M}
  /-- 選んだ同じ全 Hom dg 模型の前三角性。 -/
  pretriangulated : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R {M : ModuleCategory R D // objects M}
  /-- 同じ代表加群は全 Hom end の意味で射影的。 -/
  projective : ∀ M, objects M → _root_.SerrePositivity.DifferentialGraded.moduleHomotopicallyProjective R D M
  /-- 同じ実半自由模型への比較は、全写像空間で充満忠実。 -/
  derivedFullyFaithful : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion R (ModuleCategory R D) objects) ≫
      dgConeModuleDerived R D)
  /-- 各代表の実導来 ∞ 圏での κ-compact 性。 -/
  kappaCompact : ∀ M, objects M →
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, max (u + 1) v} κ (dgConeModuleDerivedVertex R D M)
  /-- 元の全 κ-compact 頂点を、同じ ∞ 圏での同型まで代表する。 -/
  covers : ∀ y : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D) _⦋0⦌,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, max (u + 1) v} κ y →
      ∃ M : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D, objects M ∧
        Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (dgConeModuleDerivedVertex R D M) y)
  /-- 選んだ代表系内での実可算直和の閉性。swindle の同型自体は要求しない。 -/
  countableClosed : ∀ M : ℕ → _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D, (∀ n, objects (M n)) → objects (∐ M)
  /-- 同じ代表系内での実二項直和の閉性。 -/
  binaryClosed : ∀ M N, objects M → objects N → objects (M ⨿ N)
  /-- 元の通常の perfect 導来加群を、同じ代表系内で実現する。 -/
  perfectCovers : ∀ M : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D,
    _root_.SerrePositivity.DifferentialGraded.modulePerfect R D ((_root_.SerrePositivity.DifferentialGraded.moduleToDerived R D).obj M) →
      ∃ N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D, objects N ∧
        Nonempty ((_root_.SerrePositivity.DifferentialGraded.moduleToDerived R D).obj N ≅ (_root_.SerrePositivity.DifferentialGraded.moduleToDerived R D).obj M)

end SerrePositivity.KST.NonConnective
