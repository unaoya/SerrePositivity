module
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.HomotopyInvertibility
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.HomotopyNatTrans

/-!
概要：指定 loop 単位と任意の実パラメータ族の comma 矢印の可逆性。
方針：端点輸送を Arrow の等号に保ち、同じ一次単体を照合する。
規約：追加の基準矢印の可逆性を仮定しない。使われ方：元の loop 四角形の普遍性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 同じ実ホモトピーの頂点辺を保つ comma の比較。 -/
lemma homotopyNatTransOfEndpoints_app_vertexEdge_arrow {A X : SSet.{u}} {F G : A ⟶ X}
    (H : SSet.Homotopy F G) (a : A _⦋0⦌) :
    Arrow.mk ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyNatTransOfEndpoints H.h H.h₀ H.h₁).app (HomotopyCategory.mk a)) =
      Arrow.mk (SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H a).toTruncated) := by
  have ht (U : A ⊗ (Δ[1] : SSet.{u}) ⟶ X) {f g : A ⟶ X}
      (h₀ : SSet.ι₀ ≫ U = f) (h₁ : SSet.ι₁ ≫ U = g) :
      Arrow.mk ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyNatTransOfEndpoints U h₀ h₁).app (HomotopyCategory.mk a)) =
        Arrow.mk ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyNatTrans U).app (HomotopyCategory.mk a)) := by
    subst f g
    rfl
  rw [ht]
  change Arrow.mk (SSet.Truncated.HomotopyCategory.homMk _) = _
  exact SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk _ _ rfl

/-- 同じ実ホモトピーの頂点辺を保つ comma の比較。 -/
lemma homotopyNatTransOfEndpoints_app_isIso_of_vertexEdge {A X : SSet.{u}} {F G : A ⟶ X}
    (H : SSet.Homotopy F G) (a : A _⦋0⦌)
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H a).toTruncated) :
    IsIso ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyNatTransOfEndpoints H.h H.h₀ H.h₁).app (HomotopyCategory.mk a)) :=
  Eq.mpr (congrArg (fun q : Arrow (hoFunctor.obj X) ↦ IsIso q.hom)
    (homotopyNatTransOfEndpoints_app_vertexEdge_arrow H a)) he
end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
