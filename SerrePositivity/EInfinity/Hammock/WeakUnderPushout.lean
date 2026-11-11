module

public import SerrePositivity.EInfinity.Hammock.WeakPushout
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PrecompositionUnderPushout

/-!
# 元の境界を固定した弱同値の pushout による保存

概要：境界からの二つの包含が単射なら、元の対象間の弱同値は pushout 後も弱同値。
方針：元の相対写像円柱の二つの単射と収縮で、単射の弱同値の場合へ帰着する。
規約：比較射や相手側の貼り合わせ射の単射性は仮定しない。
使われ方：二つの元の pushout の比較の弱同値性。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories

lemma weak_map_under_of_mono {A : SSet.{u}} (F : Under A ⥤ SSet.{u})
    (hF : ∀ {X Y : Under A} [Mono X.hom] [Mono Y.hom] (f : X ⟶ Y) [Mono f.right],
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence f.right → _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (F.map f))
    {X Y : Under A} [Mono X.hom] [Mono Y.hom] (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence f.right) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (F.map f) := by
  have hif : Mono (X.hom ≫ f.right) := by rw [Under.w]; infer_instance
  let Z : Under A := Under.mk (X.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.relativeEquivalenceMappingCylinderIn X.hom f.right)
  have : Mono Z.hom := by dsimp [Z]; infer_instance
  let g : X ⟶ Z := Under.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.relativeEquivalenceMappingCylinderIn X.hom f.right) rfl
  let s : Y ⟶ Z := Under.homMk
    (pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.relativeEquivalenceCylinderEndpoint X.hom false) f.right) (by
      change Y.hom ≫ _ = X.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.relativeEquivalenceMappingCylinderIn X.hom f.right
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.relativeEquivalenceMappingCylinderIn_fixed, Under.w])
  let r : Z ⟶ Y := Under.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.relativeEquivalenceMappingCylinderOut X.hom f.right) (by
    change (X.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.relativeEquivalenceMappingCylinderIn X.hom f.right) ≫ _ = Y.hom
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.relativeEquivalenceMappingCylinderIn_out, Under.w])
  have : Mono g.right := by
    change Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.relativeEquivalenceMappingCylinderIn X.hom f.right)
    infer_instance
  have : Mono s.right := by
    dsimp [s]
    exact Adhesive.mono_of_isPushout_of_mono_left (IsPushout.of_hasPushout _ _)
  have hs : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence s.right :=
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_relativeEquivalenceCylinderEndpoint X.hom false).of_isPushout
      (IsPushout.of_hasPushout _ _)).isWeakHomotopyEquivalence
  have hsr : s ≫ r = 𝟙 Y := by
    apply Under.UnderMorphism.ext
    exact pushout.inr_desc _ _ _
  have hgr : g ≫ r = f := by
    apply Under.UnderMorphism.ext
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.relativeEquivalenceMappingCylinderIn_out X.hom f.right
  have hsr' := congrArg (fun h : Y ⟶ Y => h.right) hsr
  have hgr' := congrArg (fun h : X ⟶ Y => h.right) hgr
  change s.right ≫ r.right = 𝟙 Y.right at hsr'
  change g.right ≫ r.right = f.right at hgr'
  have hrRight : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence r.right := by
    apply hs.cancel_left
    rw [hsr']
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.isWeakHomotopyEquivalence_id _
  have hg : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence g.right := by
    apply hrRight.cancel_right
    rw [hgr']
    exact hf
  have hr : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (F.map r) := by
    apply (hF s hs).cancel_left
    rw [← F.map_comp, hsr, F.map_id]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.isWeakHomotopyEquivalence_id _
  have h := (hF g hg).comp hr
  rwa [← F.map_comp, hgr] at h

def monoWeakHomotopyEquivalences : MorphismProperty SSet.{u} :=
  fun _ _ f => Mono f ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence f

lemma monoWeakHomotopyEquivalences_cobase :
    monoWeakHomotopyEquivalences.{u}.IsStableUnderCobaseChange where
  of_isPushout h hf := by
    have := hf.1
    exact ⟨Adhesive.mono_of_isPushout_of_mono_left h.flip, weakPushout_mono hf.2 h.flip⟩

lemma weak_underPushout_map {A C : SSet.{u}} (g : A ⟶ C)
    {X Y : Under A} [Mono X.hom] [Mono Y.hom] (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence f.right) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (((Under.pushout g).map f).right) := by
  apply weak_map_under_of_mono (Under.pushout g ⋙ Under.forget C) ?_ f hf
  intro X Y _ _ k _ hk
  have := monoWeakHomotopyEquivalences_cobase.{u}
  exact (monoWeakHomotopyEquivalences.underPushoutMap g k ⟨inferInstance, hk⟩).2

lemma weakPushout_fixed_base {A B B' C D D' : SSet.{u}}
    {i : A ⟶ B} {i' : A ⟶ B'} [Mono i] [Mono i'] {g : A ⟶ C}
    {r : B ⟶ D} {s : C ⟶ D} {r' : B' ⟶ D'} {s' : C ⟶ D'}
    (hP : IsPushout i g r s) (hP' : IsPushout i' g r' s')
    (f : B ⟶ B') (h : D ⟶ D') (hi : i ≫ f = i')
    (hr : r ≫ h = f ≫ r') (hs : s ≫ h = s')
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence f) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence h := by
  have : Mono (Under.mk i).hom := by change Mono i; infer_instance
  have : Mono (Under.mk i').hom := by change Mono i'; infer_instance
  let v : Under.mk i ⟶ Under.mk i' := Under.homMk f hi
  let m := ((Under.pushout g).map v).right
  have hm : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence m := weak_underPushout_map g v hf
  have hm₁ : pushout.inl i g ≫ m = f ≫ pushout.inl i' g := pushout.inl_desc _ _ _
  have hm₂ : pushout.inr i g ≫ m = pushout.inr i' g := pushout.inr_desc _ _ _
  have he : hP.isoPushout.hom ≫ m ≫ hP'.isoPushout.inv = h := by
    apply hP.hom_ext
    · rw [← Category.assoc, ← Category.assoc, hP.inl_isoPushout_hom, Category.assoc,
        ← Category.assoc, hm₁, Category.assoc, hP'.inl_isoPushout_inv, hr]
    · rw [← Category.assoc, ← Category.assoc, hP.inr_isoPushout_hom, Category.assoc,
        ← Category.assoc, hm₂, hP'.inr_isoPushout_inv, hs]
  rw [← he]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso hP.isoPushout).isWeakHomotopyEquivalence.comp
    (hm.comp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso hP'.isoPushout.symm).isWeakHomotopyEquivalence)

end SerrePositivity.EInfinity.Hammock
