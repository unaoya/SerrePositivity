module

public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NerveSmallFamilies

/-!
# 中断した任意モデル源への一般化：NerveLargeSampling

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Small full test families of a coherent system with a large constant parameter。

## 方針（定義・証明）
bar型の鎖パラメータと整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0477][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0477
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Small full test families of a coherent system with a large constant parameter
-/

@[expose] public section
universe w v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open SerrePositivity.NerveSimplexEndpoint

namespace SerrePositivity.SimplicialModel.NerveLargeSampling
variable {D : Type uD} [Category.{vD} D] (F : D ⥤ SSet.{v}) {K : SSet.{max w v}}
  (a : NerveLargeParameter.System.{w, v} F K)

/-- The same constant-parameter system viewed in the moving-parameter diagram. -/
def moving : NerveMovingParameter.System.{w, v} ((Functor.const D).obj K) F where
  app s := a.app s
  naturality {s t} f := by
    change SSet.stdSimplex.map (operator f) ≫ a.app t =
      a.app s ≫ (pre (𝟙 K)).app (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} (F.obj (endpoint s))) ≫
        (ihom K).map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{w} (F.map (endpointMap f)))
    rw [pre_id]
    exact (a.naturality f).trans (congrArg (fun z => a.app s ≫ z)
      (Category.id_comp ((ihom K).map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{w} (F.map (endpointMap f))))).symm)

variable {P : SSet.{v}} (k : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} P ⟶ K)

/-- Retain the entire prescribed small test, rather than only one of its simplices. -/
def system : NerveMovingParameter.System.{w, v}
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted.{w} ((Functor.const D).obj P)) F :=
  NerveBiparameterMaps.restrict _ _ _ ((Functor.const D).map k) (moving F a)

def family {n : ℕ} (c : ComposableArrows D n) :
    P ⊗ SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶ F.obj (c.obj (Fin.last n)) :=
  NerveSmallFamilies.family ((Functor.const D).obj P) F (system F a k) c

lemma family_naturality {n m : ℕ} (c : ComposableArrows D n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    P ◁ SSet.stdSimplex.map θ ≫ family F a k c =
    family F a k ((SimplexCategory.toCat.map θ).toFunctor ⋙ c) ≫
      F.map (c.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last m))))) := by
  have h := NerveSmallFamilies.family_naturality ((Functor.const D).obj P) F (system F a k) c θ
  change P ◁ SSet.stdSimplex.map θ ≫ family F a k c =
    ((𝟙 P ▷ SSet.stdSimplex.obj (SimplexCategory.mk m)) ≫
      family F a k ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)) ≫
      F.map (c.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last m))))) at h
  rw [id_whiskerRight, Category.id_comp] at h
  exact h

lemma point (d : D) : NerveSmallFamilies.point ((Functor.const D).obj P) F (system F a k) d =
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.lower (k ≫ NerveParameterExtension.evaluate (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveLargeParameter.lifted.{w} F) a d)
      := by
  have he : NerveMovingParameter.evaluate
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted.{w} ((Functor.const D).obj P)) F (system F a k) d =
      k ≫ NerveParameterExtension.evaluate (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveLargeParameter.lifted.{w} F) a d :=
    NerveBiparameterMaps.evaluate_restrict _ _ _ _ _ d
  exact congrArg _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.lower he

lemma family_lift {n : ℕ} (c : ComposableArrows D n) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexTensorMap.{w} (family F a k c) =
    (k ▷ SSet.stdSimplex.obj (SimplexCategory.mk n)) ≫ uncurry (a.app (ofChain c)) :=
  (NerveSmallFamilies.family_lift _ _ _ c).trans
    (uncurry_pre_app (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} (F.obj (c.obj (Fin.last n))))
      (a.app (ofChain c)) k)

lemma system_precomp {Q : SSet.{v}} (q : Q ⟶ P) : system F a (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{w} q ≫ k) =
    NerveBiparameterMaps.restrict _ _ _
      (Functor.whiskerRight ((Functor.const D).map q) SSet.uliftFunctor.{w, v})
      (system F a k) := by
  change moving F a ≫ NerveBiparameterMaps.restriction _ _ _ _ =
    (moving F a ≫ NerveBiparameterMaps.restriction _ _ _ _) ≫
      NerveBiparameterMaps.restriction _ _ _ _
  rw [Category.assoc, NerveBiparameterMaps.restriction_comp]
  rfl

lemma family_precomp {Q : SSet.{v}} (q : Q ⟶ P) {n : ℕ} (c : ComposableArrows D n) :
    family F a (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{w} q ≫ k) c =
      (q ▷ SSet.stdSimplex.obj (SimplexCategory.mk n)) ≫ family F a k c :=
  (congrArg (fun z => NerveSmallFamilies.family ((Functor.const D).obj Q) F z c)
    (system_precomp F a k q)).trans (NerveSmallFamilies.family_restrict _ _ _ _ _ c)

lemma system_restrict {L : SSet.{max w v}} (i : L ⟶ K) (l : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} P ⟶ L) :
    system F (NerveLargeParameter.restrict F a i) l = system F a (l ≫ i) := by
  apply NatTrans.ext
  funext s
  change (a.app s ≫ (pre i).app _) ≫ (pre l).app _ =
    a.app s ≫ (pre (l ≫ i)).app _
  rw [Category.assoc]
  exact congrArg (fun z => a.app s ≫ z)
    (RelativeChoiceSpace.restriction_comp (P := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} (F.obj (endpoint s))) l i)

lemma family_restrict {L : SSet.{max w v}} (i : L ⟶ K) (l : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} P ⟶ L)
    {n : ℕ} (c : ComposableArrows D n) :
    family F (NerveLargeParameter.restrict F a i) l c = family F a (l ≫ i) c :=
  congrArg (fun z => NerveSmallFamilies.family ((Functor.const D).obj P) F z c)
    (system_restrict F a i l)

end SerrePositivity.SimplicialModel.NerveLargeSampling
