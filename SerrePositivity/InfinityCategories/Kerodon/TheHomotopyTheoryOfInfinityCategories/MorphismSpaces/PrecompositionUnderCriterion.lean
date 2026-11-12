module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.RelativeMappingCylinder

/-!
概要：固定部分を保つ関手の同値の保存の単射上での判定。
方針：相対写像円柱により、固定部分の包含が単射な対象間の射を扱う。
規約：固定部分からの二つの包含の単射性を明記する。
使われ方：Kerodon §4.6.2（Tag 01HM） の境界を保つ貼り合わせ。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：固定部分を持つ対象間の関手の同値保存は単射の射だけで判定できる。
方針：相対写像円柱の二つの単射と収縮に二対三則を適用する。
規約：固定部分からの二つの射も単射であることを要求する。
使われ方：Kerodon §4.6.2（Tag 01HM） の境界を固定した同値比較。 -/
lemma isPrecompositionEquivalence_map_under_of_mono {A : SSet.{u}}
    (F : Under A ⥤ SSet.{u})
    (hF : ∀ {X Y : Under A} [Mono X.hom] [Mono Y.hom] (f : X ⟶ Y) [Mono f.right],
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence f.right → _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (F.map f))
    {X Y : Under A} [Mono X.hom] [Mono Y.hom] (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence f.right) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (F.map f) := by
  have hif : Mono (X.hom ≫ f.right) := by rw [Under.w]; infer_instance
  let Z : Under A := Under.mk
    (X.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.relativeEquivalenceMappingCylinderIn X.hom f.right)
  have : Mono Z.hom := by dsimp [Z]; infer_instance
  let g : X ⟶ Z := Under.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.relativeEquivalenceMappingCylinderIn X.hom f.right) rfl
  let s : Y ⟶ Z := Under.homMk
    (pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.relativeEquivalenceCylinderEndpoint X.hom false) f.right) (by
      change Y.hom ≫ _ = X.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.relativeEquivalenceMappingCylinderIn X.hom f.right
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.relativeEquivalenceMappingCylinderIn_fixed, Under.w])
  let r : Z ⟶ Y := Under.homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.relativeEquivalenceMappingCylinderOut X.hom f.right) (by
      change (X.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.relativeEquivalenceMappingCylinderIn X.hom f.right) ≫ _ = Y.hom
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.relativeEquivalenceMappingCylinderIn_out, Under.w])
  have : Mono g.right := by
    change Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.relativeEquivalenceMappingCylinderIn X.hom f.right)
    infer_instance
  have : Mono s.right := by
    dsimp [s]
    exact Adhesive.mono_of_isPushout_of_mono_left (IsPushout.of_hasPushout _ _)
  have hs : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence s.right :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_relativeEquivalenceCylinderEndpoint X.hom false).of_isPushout
      (IsPushout.of_hasPushout _ _)
  have hg : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence g.right :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_iff_relativeEquivalenceMappingCylinderIn X.hom f.right).mp hf
  have hsr : s ≫ r = 𝟙 Y := by
    apply Under.UnderMorphism.ext
    exact pushout.inr_desc _ _ _
  have hgr : g ≫ r = f := by
    apply Under.UnderMorphism.ext
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.relativeEquivalenceMappingCylinderIn_out X.hom f.right
  have hr : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (F.map r) := by
    apply (hF s hs).cancel_left
    rw [← F.map_comp, hsr, F.map_id]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_id _
  have h := (hF g hg).comp hr
  rwa [← F.map_comp, hgr] at h

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
