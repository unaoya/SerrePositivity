module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleKappaCompactTransport
/-!
概要：主導来加群圏の同型を、同じ実導来頂点の κ-compact 性へ輸送する。
方針：実半自由模型の充満忠実な h 比較で指定同型を引き戻し、元の全 Hom 定義へ戻す。
規約：主導来圏の ordinary compact 性を使用せず、比較は頂点同型の構成にだけ使う。
使われ方：D-8 c の perfect 代表の変更と、実加群の導来同型による κ-compact 性の移送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open _root_.SerrePositivity.KST.NonConnective
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]

/-- 同じ半自由 dg nerve の通常の h から、主導来加群圏への比較。 -/
abbrev dgModuleDerivedHoComparison :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableHomotopyEquivalence R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)).functor ⋙
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeModuleToDerived R D

/-- 同じ加群の実導来頂点の比較像は、元の指定主導来像に同型。 -/
def dgConeModuleDerivedVertex_classicalIso (M : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D) :
    (dgModuleDerivedHoComparison R D).obj
      (SSet.HomotopyCategory.mk (dgConeModuleDerivedVertex R D M)) ≅
        (_root_.SerrePositivity.DifferentialGraded.moduleToDerived R D).obj M := by
  let X : hoFunctor.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (ModuleCategory R D)) :=
    SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex M)
  let F := dgConeModuleForget R D
  let a := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_classicalIso R (ModuleCategory R D) D F
  let b := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolutionClassicalComparisonIso R (ModuleCategory R D) D F
  exact a.app X ≪≫ b.app ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableHomotopyEquivalence R (ModuleCategory R D)).functor.obj X) ≪≫
    (_root_.SerrePositivity.DifferentialGraded.moduleToHomotopyDerivedIso R D).app M

/-- 主導来圏の指定同型を、元の二つの実導来頂点の同型へ戻す。 -/
def dgConeModuleDerivedVertexIsoOfDerivedIso {M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D}
    (e : (_root_.SerrePositivity.DifferentialGraded.moduleToDerived R D).obj M ≅ (_root_.SerrePositivity.DifferentialGraded.moduleToDerived R D).obj N) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (dgConeModuleDerivedVertex R D M) (dgConeModuleDerivedVertex R D N) :=
  (dgModuleDerivedHoComparison R D).preimageIso
    (dgConeModuleDerivedVertex_classicalIso R D M ≪≫ e ≪≫
      (dgConeModuleDerivedVertex_classicalIso R D N).symm)

/-- 主導来像が同型な加群は、元の全共変 Hom に関して同じ κ-compact 性を持つ。 -/
lemma dgModuleKappaCompact_iff_of_derivedIso {κ : Cardinal.{u}}
    {M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D}
    (e : (_root_.SerrePositivity.DifferentialGraded.moduleToDerived R D).obj M ≅ (_root_.SerrePositivity.DifferentialGraded.moduleToDerived R D).obj N) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact R D κ M ↔ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact R D κ N :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact_iff_of_vertexIso R D (dgConeModuleDerivedVertexIsoOfDerivedIso R D e)

/-- 主導来圏の実 retract を、元の実導来頂点の h 圏内の retract へ戻す。 -/
def dgConeModuleDerivedVertexRetractionOfDerivedRetract {M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D}
    (r : Retract ((_root_.SerrePositivity.DifferentialGraded.moduleToDerived R D).obj M) ((_root_.SerrePositivity.DifferentialGraded.moduleToDerived R D).obj N)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.VertexRetraction
      (dgConeModuleDerivedVertex R D M) (dgConeModuleDerivedVertex R D N) := by
  let H := dgModuleDerivedHoComparison R D
  let s := (Retract.ofIso (dgConeModuleDerivedVertex_classicalIso R D M)).trans
    (r.trans (Retract.ofIso (dgConeModuleDerivedVertex_classicalIso R D N).symm))
  refine ⟨H.preimage s.i, H.preimage s.r, ?_⟩
  apply H.map_injective
  rw [H.map_comp, H.map_preimage, H.map_preimage, s.retract, H.map_id]

/-- 主導来像の実 retract は、元の全 Hom による κ-compact 性を保つ。 -/
lemma dgModuleKappaCompact_of_derivedRetract {κ : Cardinal.{u}}
    {M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D}
    (r : Retract ((_root_.SerrePositivity.DifferentialGraded.moduleToDerived R D).obj M) ((_root_.SerrePositivity.DifferentialGraded.moduleToDerived R D).obj N))
    (hN : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact R D κ N) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact R D κ M :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact_of_vertexRetract R D
    ⟨dgConeModuleDerivedVertexRetractionOfDerivedRetract R D r⟩ hN

end SerrePositivity.InfinityCategories.Project.DerivedCategories
