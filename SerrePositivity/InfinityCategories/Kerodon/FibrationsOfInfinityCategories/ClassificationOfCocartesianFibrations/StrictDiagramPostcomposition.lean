module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.StrictDiagramMappingVertices

/-!
概要：通常の自然変換による strict な変換空間の後合成。
方針：内部 Hom の共通パラメーターで成分を後合成する。
規約：係数の Kan 性は不要。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、strict な逆変換の二つの比較の接続。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：strict な変換を通常の自然変換で後合成する。
方針：各対象のパラメーター付きの変換の後に η の成分を作用させる。
規約：η:G→H により F から G への変換を F から H へ写す。
使われ方：Kerodon §5.3.1（Tag 035D）、strict な変換空間の共変作用。 -/
def strictDiagramMappingPost {C : Type u} [Category.{u} C]
    {G H : C ⥤ SSet.{u}} (η : G ⟶ H) (F : C ⥤ SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSpace F G ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSpace F H where
  app _ := ↾fun θ ↦ ⟨fun c ↦
    Functor.HomObj.comp (θ.val c) (Functor.HomObj.ofNatTrans (η.app c)), by
      intro c d f k α x
      change (H.map f).app k ((η.app c).app k ((θ.val c).app k α x)) =
        (η.app d).app k ((θ.val d).app k α ((F.map f).app k x))
      have h := congrArg (fun a : G.obj c ⟶ H.obj d ↦
        a.app k ((θ.val c).app k α x)) (η.naturality f)
      exact h.symm.trans (congrArg ((η.app d).app k) (θ.property f k α x))⟩
  naturality {n m} α := by
    apply ConcreteCategory.hom_ext
    intro θ
    apply Subtype.ext
    funext c
    apply CategoryTheory.Functor.functorHom_ext
    intro k β
    apply ConcreteCategory.hom_ext
    intro x
    rfl

/-- 概要：strict な変換空間の後合成は通常の変換の合成の頂点を与える。
方針：各対象の内部 Hom の零単体で後合成を計算する。
規約：θ の後に η を合成する。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、逆変換の片側の比較を他方へ移す。 -/
lemma strictDiagramMappingPost_vertex {C : Type u} [Category.{u} C]
    {F G H : C ⥤ SSet.{u}} (η : G ⟶ H) (θ : F ⟶ G) :
    (strictDiagramMappingPost η F).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMappingVertex θ) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMappingVertex (θ ≫ η) := rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
