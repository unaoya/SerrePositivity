module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardPathPushout

/-!
# 始点を動かす元の forward 射列の pushout の関手性

概要：元の射列・始点置換・その可換四角形を同時に動かす比較を関手へ束ねる。
方針：全頂点の pushout.map と元の二つの包含で自然性・恒等・合成を照合する。
規約：元の始点も動かす。全対象と全射への同時の構成である。
使われ方：自明 cofibration の右の forward ブロックへの関手的伝播。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [HasPushouts C] {n : ℕ}

omit [HasPushouts C] in
lemma initialLeg_comparison {F G : ComposableArrows C n} (η : F ⟶ G) (i : Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.initialLeg F i ≫ η.app i = η.app 0 ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.initialLeg G i :=
  η.naturality (homOfLE (Fin.zero_le i))

variable {s t r : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InitialReplacement C n} (m : s ⟶ t)

def pushoutComparisonApp (i : Fin (n + 1)) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pushoutObj s i ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pushoutObj t i :=
  pushout.map s.hom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.initialLeg s.left i) t.hom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.initialLeg t.left i)
    m.right (m.left.app i) (m.left.app 0) m.w.symm (initialLeg_comparison m.left i)

lemma pushoutComparisonApp_inl (i : Fin (n + 1)) :
    pushout.inl s.hom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.initialLeg s.left i) ≫ pushoutComparisonApp m i =
      m.right ≫ pushout.inl t.hom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.initialLeg t.left i) := pushout.inl_desc _ _ _

lemma pushoutComparisonApp_inr (i : Fin (n + 1)) :
    pushout.inr s.hom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.initialLeg s.left i) ≫ pushoutComparisonApp m i =
      m.left.app i ≫ pushout.inr t.hom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.initialLeg t.left i) := pushout.inr_desc _ _ _

lemma pushoutComparisonApp_naturality {i j : Fin (n + 1)} (f : i ⟶ j) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pushoutArrow s f ≫ pushoutComparisonApp m j =
      pushoutComparisonApp m i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pushoutArrow t f := by
  apply pushout.hom_ext
  · calc
      _ = m.right ≫ pushout.inl t.hom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.initialLeg t.left j) := by
        rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pushoutArrow_inl, pushoutComparisonApp_inl]
      _ = _ := by
        symm
        rw [← Category.assoc, pushoutComparisonApp_inl, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pushoutArrow_inl]
  · calc
      _ = (s.left.map f ≫ m.left.app j) ≫ pushout.inr t.hom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.initialLeg t.left j) := by
        rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pushoutArrow_inr, Category.assoc,
          pushoutComparisonApp_inr, ← Category.assoc]
      _ = (m.left.app i ≫ t.left.map f) ≫ pushout.inr t.hom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.initialLeg t.left j) := by
        rw [m.left.naturality f]
      _ = _ := by
        symm
        rw [← Category.assoc, pushoutComparisonApp_inr, Category.assoc,
          _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pushoutArrow_inr, ← Category.assoc]

def pushoutComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pushoutPath s ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pushoutPath t where
  app := pushoutComparisonApp m
  naturality _ _ f := pushoutComparisonApp_naturality m f

def pushoutFunctor : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InitialReplacement C n ⥤ ComposableArrows C n where
  obj := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pushoutPath
  map := pushoutComparison
  map_id s := by
    apply NatTrans.ext
    funext i
    apply pushout.hom_ext
    · change _ ≫ pushoutComparisonApp (𝟙 s) i = _ ≫ (𝟙 _)
      rw [pushoutComparisonApp_inl]
      simp
    · change _ ≫ pushoutComparisonApp (𝟙 s) i = _ ≫ (𝟙 _)
      rw [pushoutComparisonApp_inr]
      simp
  map_comp m k := by
    apply NatTrans.ext
    funext i
    apply pushout.hom_ext
    · change _ ≫ pushoutComparisonApp (m ≫ k) i =
        _ ≫ (pushoutComparisonApp m i ≫ pushoutComparisonApp k i)
      rw [pushoutComparisonApp_inl, ← Category.assoc, pushoutComparisonApp_inl,
        Category.assoc, pushoutComparisonApp_inl, ← Category.assoc]
      rfl
    · change _ ≫ pushoutComparisonApp (m ≫ k) i =
        _ ≫ (pushoutComparisonApp m i ≫ pushoutComparisonApp k i)
      rw [pushoutComparisonApp_inr, ← Category.assoc, pushoutComparisonApp_inr,
        Category.assoc, pushoutComparisonApp_inr, ← Category.assoc]
      rfl

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
