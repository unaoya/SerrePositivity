module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.StrictDiagramPrecomposition
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.StrictDiagramComposition

/-!
概要：strict な変換空間の頂点と通常の自然変換の対応。
方針：対象ごとの内部 Hom の頂点の対応を、自然性の条件に制限する。
規約：係数図式の Kan 性は不要。
使われ方：Kerodon §5.3.1（Tag 035D）、Corollary 5.6.0.6（Tag 028T）、写像空間の同値から逆変換を取り出す。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：通常の自然変換を strict な変換空間の頂点にする。
方針：成分の関手頂点に自然性の条件を添える。
規約：始域と終域の図式は任意。
使われ方：Kerodon §5.3.1（Tag 035D）、自然変換の高次空間での表示。 -/
def strictDiagramMappingVertex {C : Type u} [Category.{u} C]
    {F G : C ⥤ SSet.{u}} (η : F ⟶ G) : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSpace F G) _⦋0⦌ :=
  ⟨fun c ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (η.app c), by
    intro c d f k α x
    exact (congrArg (fun a : F.obj c ⟶ G.obj d ↦ a.app k x) (η.naturality f)).symm⟩

/-- 概要：strict な変換空間の全ての頂点は通常の自然変換から得られる。
方針：各成分の内部 Hom の頂点を射へ戻し、固定した単体の入力で自然性を検証する。
規約：成分の選択は内部 Hom の標準の全単射による。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、前合成同値の本質的全射性から逆変換を得る。 -/
lemma exists_strictDiagramMappingVertex {C : Type u} [Category.{u} C]
    (F G : C ⥤ SSet.{u}) (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSpace F G) _⦋0⦌) :
    ∃ η : F ⟶ G, strictDiagramMappingVertex η = v := by
  let ηc := fun c ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (F.obj c) (G.obj c)).symm (v.val c)
  have hv (c : C) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (ηc c) = v.val c :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (F.obj c) (G.obj c)).apply_symm_apply (v.val c)
  let η : F ⟶ G :=
    { app := ηc
      naturality c d f := by
        apply SSet.hom_ext
        intro k
        apply ConcreteCategory.hom_ext
        intro x
        have h := v.property f k (SimplexCategory.const k.unop ⦋0⦌ 0).op x
        rw [← hv c, ← hv d] at h
        exact h.symm }
  refine ⟨η, ?_⟩
  apply Subtype.ext
  funext c
  exact hv c

/-- 概要：strict な変換空間の前合成は通常の変換の合成の頂点を与える。
方針：各対象の内部 Hom の零単体で合成を計算する。
規約：η の後に θ を合成する。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、写像空間の単位・余単位を変換の合成へ戻す。 -/
lemma strictDiagramMappingPre_vertex {C : Type u} [Category.{u} C]
    {F G H : C ⥤ SSet.{u}} (η : F ⟶ G) (θ : G ⟶ H) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMappingPre η H).app _ (strictDiagramMappingVertex θ) =
      strictDiagramMappingVertex (η ≫ θ) := rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
