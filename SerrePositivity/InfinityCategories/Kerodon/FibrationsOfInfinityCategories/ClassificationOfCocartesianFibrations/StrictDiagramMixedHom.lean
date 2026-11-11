module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.StrictDiagramComposition

/-!
概要：strict な図式の変換と底の射の共同評価。
方針：始点で変換を評価し、終域図式の底の射を後合成する。
規約：係数図式は同じ通常の圏から単体集合への共変関手。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、straightening の像の対角評価。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：strict な変換を底の射に沿って混合評価する。
方針：変換の始点成分に終域図式の輸送を後合成する。
規約：f は c から d への射。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、底と変換を同時に動かす Hom 写像。 -/
def strictDiagramMixedHom {C : Type u} [Category.{u} C] {c d : C}
    (f : c ⟶ d) (F G : C ⥤ SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSpace F G ⟶ (ihom (F.obj c)).obj (G.obj d) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingComponent F G c ≫ (ihom (F.obj c)).map (G.map f)

/-- 概要：混合評価は底と変換の恒等射を保つ。
方針：図式の恒等射保存と成分の豊穣単位を使う。
規約：底の対象 c を固定する。
使われ方：Kerodon §5.3.1（Tag 035D）、対角評価の豊穣単位則。 -/
lemma strictDiagramMixedHom_id {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) (c : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMappingIdentity F ≫ strictDiagramMixedHom (𝟙 c) F F =
      MonoidalClosed.id (F.obj c) := by
  simp only [strictDiagramMixedHom, F.map_id]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMappingIdentity_component F c

/-- 概要：混合評価は底の合成と変換の豊穣合成に整合する。
方針：内部 Hom を uncurry し、後段の変換の自然性で輸送の順を交換する。
規約：f の後に g を合成し、F から G、次に H への変換を評価する。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、共同評価の豊穣合成則。 -/
lemma strictDiagramMixedHom_comp {C : Type u} [Category.{u} C] {c d e : C}
    (f : c ⟶ d) (g : d ⟶ e) (F G H : C ⥤ SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMappingComposition F G H ≫ strictDiagramMixedHom (f ≫ g) F H =
      (strictDiagramMixedHom f F G ⊗ₘ strictDiagramMixedHom g G H) ≫
        MonoidalClosed.comp (F.obj c) (G.obj d) (H.obj e) := by
  apply uncurry_injective
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨x, η, θ⟩
  change (H.map (f ≫ g)).app n
      ((θ.val c).app n (𝟙 n) ((η.val c).app n (𝟙 n) x)) =
    (H.map g).app n ((θ.val d).app n (𝟙 n)
      ((G.map f).app n ((η.val c).app n (𝟙 n) x)))
  rw [H.map_comp]
  exact congrArg (fun z ↦ (H.map g).app n z)
    (θ.property f n (𝟙 n) ((η.val c).app n (𝟙 n) x))

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
