module

public import SerrePositivity.InfinityCategories.F1.Diagrams.StrictDiagramPrecomposition
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorRestrictionFibration

/-!
概要：strict transport を標的とする変換空間の、単射な図式の制限に関する持ち上げ性。
方針：scaffold の同型で相対写像空間へ移し、replacement の単射性と相対制限の持ち上げ性を使う。
規約：モデル構造を導入せず、全境界または全ホーンの持ち上げ性として述べる。
使われ方：Kerodon §§5.3.1、5.6.5、固定した比較を保つ高次パラメーター付き延長。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：対象ごとに単射な自然変換は replacement の全空間の単射を誘導する。
方針：底の射列を比較してから、係数単体への後合成の単射性を使う。
規約：係数図式の Kan 性は不要。
使われ方：Kerodon §5.3.2、図式の包含から相対写像空間の制限を作る。 -/
instance simplicialReplacementMap_mono {C : Type u} [Category.{u} C]
    {F G : C ⥤ SSet.{u}} (η : F ⟶ G) [∀ c, Mono (η.app c)] :
    Mono (simplicialReplacementMap η) := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  rw [mono_iff_injective]
  rintro ⟨σ, τ⟩ ⟨σ', τ'⟩ h
  change (⟨σ, τ ≫ η.app (σ.obj 0)⟩ : simplicialReplacementSimplex G _) =
    ⟨σ', τ' ≫ η.app (σ'.obj 0)⟩ at h
  have hσ := congrArg Sigma.fst h
  cases hσ
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  apply (cancel_mono (η.app (σ.obj 0))).1
  exact eq_of_heq (Sigma.mk.inj_iff.mp h).2

/-- 概要：strict な図式の制限は scaffold 同型の間に相対前合成を挟んだ射そのもの。
方針：scaffold の順方向を後合成し、既存の自然性の式と同型の往復を使う。
規約：q の充填性は要求しない。
使われ方：Kerodon Corollary 5.6.0.6、制限の全境界持ち上げ性を相対 Hom から移す。 -/
lemma strictDiagramMappingPre_scaffold_factorization {C : Type u} [Category.{u} C]
    {F G : C ⥤ SSet.{u}} (η : F ⟶ G) {E : SSet.{u}} (q : E ⟶ nerve C) :
    strictDiagramMappingPre η (leftStrictTransportDiagram q) =
      (strictDiagramMappingScaffoldIso G q).hom ≫
        relativeFunctorPre q (simplicialReplacementProjection G) (simplicialReplacementMap η) ≫
          (strictDiagramMappingScaffoldIso F q).inv := by
  apply (cancel_mono (strictDiagramMappingScaffoldIso F q).hom).1
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact strictDiagramMappingPre_scaffold η q

/-- 概要：対象ごとに単射な変換による strict transport への変換空間の制限は left fibration。
方針：replacement の単射性と相対制限の left fibration 性を scaffold 同型で移す。
規約：係数の二図式の Kan 性を要求しない。
使われ方：Kerodon §§5.3.1、5.6.5、部分図式を固定した高次の比較の持ち上げ。 -/
instance strictDiagramMappingPre_leftFibration {C : Type u} [Category.{u} C]
    {F G : C ⥤ SSet.{u}} (η : F ⟶ G) [∀ c, Mono (η.app c)]
    {E : SSet.{u}} (q : E ⟶ nerve C) [LeftFibration q] :
    LeftFibration (strictDiagramMappingPre η (leftStrictTransportDiagram q)) := by
  rw [strictDiagramMappingPre_scaffold_factorization]
  exact ⟨leftFibrations.comp_mem _ _
    (leftFibrations.of_isIso (strictDiagramMappingScaffoldIso G q).hom)
    (leftFibrations.comp_mem _ _ LeftFibration.mem
      (leftFibrations.of_isIso (strictDiagramMappingScaffoldIso F q).inv))⟩

/-- 概要：対象ごとに単射な同値による strict な図式の制限は全境界を持ち上げる。
方針：replacement の単射な前合成同値に対する相対制限の判定を scaffold 同型で移す。
規約：係数の両図式は Kan 値、標的は left fibration の strict transport。
使われ方：Kerodon §§5.6.5–5.6.8、境界を固定した比較の存在と高次の一意性。 -/
lemma strictDiagramMappingPre_trivialKanFibration {C : Type u} [Category.{u} C]
    {F G : C ⥤ SSet.{u}} [∀ c, KanComplex (F.obj c)] [∀ c, KanComplex (G.obj c)]
    (η : F ⟶ G) [∀ c, Mono (η.app c)] (hη : ∀ c, IsQCatEquivalence (η.app c))
    {E : SSet.{u}} (q : E ⟶ nerve C) [LeftFibration q] :
    TrivialKanFibration (strictDiagramMappingPre η (leftStrictTransportDiagram q)) := by
  rw [strictDiagramMappingPre_scaffold_factorization]
  have h := relativeFunctorPre_trivialKanFibration_of_precompositionEquivalence q
    (simplicialReplacementProjection G) (simplicialReplacementMap η)
    (simplicialReplacementMap_isPrecompositionEquivalence η hη)
  exact ⟨trivialKanFibrations.comp_mem _ _ (TrivialKanFibration.mem (p :=
    (strictDiagramMappingScaffoldIso G q).hom))
    (trivialKanFibrations.comp_mem _ _ h.mem (TrivialKanFibration.mem (p :=
      (strictDiagramMappingScaffoldIso F q).inv)))⟩

end SerrePositivity.InfinityCategories
