module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.NativeRetract
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.NerveInclusion
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FilteredPosetNerve

/-!
概要：通常の実加群図式を固定したまま、D-bar の native/strict 比較の消費型を記述する。
方針：閉零圏の nerve 包含と正本の実分解関手を合成する。
規約：この比較の存在は証明せず明示引数に保持する。使われ方：D-8 d の native 表示。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers
open CategoryTheory Limits DifferentialGraded SSet
open _root_.SerrePositivity.KST.NonConnective
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]

/-- 元の閉零圏の対象に、同じ dg Hom を保つ閉零ラベルを一つ付ける。 -/
def dgKappaModuleClosedRelabel : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D ⥤ _root_.SerrePositivity.DifferentialGraded.ClosedCategory R (_root_.SerrePositivity.DifferentialGraded.ModuleCategory R D) where
  obj M := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) M
  map f := ForgetEnrichment.homOf (_root_.SerrePositivity.DifferentialGraded.Complex R) (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex R) f)

/-- 同じ通常の図式を全単体上で正本の実導来 ∞ 圏へ送る。 -/
def dgKappaStrictModuleDiagram {J : Type u} [Category J] (F : J ⥤ _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D) :
    (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve J) ⟶
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D :=
  (show (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve J) ⟶
      nerve (_root_.SerrePositivity.DifferentialGraded.ClosedCategory R (_root_.SerrePositivity.DifferentialGraded.ModuleCategory R D)) from {
    app _ := ↾fun s => (s.down ⋙ F) ⋙ dgKappaModuleClosedRelabel R D }) ≫
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion R (ModuleCategory R D) ≫ dgConeModuleDerived R D

lemma dgKappaStrictModuleDiagram_vertex {J : Type u} [Category J]
    (F : J ⥤ _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D) (i : (nerve J) _⦋0⦌) :
    (dgKappaStrictModuleDiagram R D F).app (Opposite.op ⦋0⦌) (ULift.up i) =
      dgConeModuleDerivedVertex R D (F.obj (i.obj 0)) := by
  change (dgConeModuleDerived R D).app _
    ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion R (ModuleCategory R D)).app _
      ((i ⋙ F) ⋙ dgKappaModuleClosedRelabel R D)) = _
  apply congrArg ((dgConeModuleDerived R D).app _)
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv R (ModuleCategory R D)).injective
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion_vertex]
  rfl

/-- D-bar に要求する最小の結論：固定した同じ strict 図式の native 余極限と頂点比較。
この命題自体の証明を追加したものではない。 -/
def DGKappaStrictFilteredColimitComparison (κ : Cardinal.{u}) [Fact κ.IsRegular] : Prop :=
  ∀ (J : Type u) [PartialOrder J] [IsCardinalFiltered J κ]
    (F : J ⥤ _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D) (c : Cocone F), IsColimit c →
    ∃ t : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (dgKappaStrictModuleDiagram R D F), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone t ∧
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso t.vertex (dgConeModuleDerivedVertex R D c.pt))

end SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers
