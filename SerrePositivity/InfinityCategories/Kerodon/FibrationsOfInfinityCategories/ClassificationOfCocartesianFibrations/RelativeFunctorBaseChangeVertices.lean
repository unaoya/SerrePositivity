module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorBaseChange
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorVertices

/-!
概要：相対関手空間の底変換同型の通常の射での計算。
方針：相対関手頂点を展開し、引き戻しの射影と持ち上げを比較する。
規約：可換性の証明は証明無関係性で同定する。
使われ方：Kerodon Remark 5.6.2.18（Tag 0271）、coherent な変換の具体的な持ち上げの終点の計算。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：固定する底の図式の等式による相対関手空間の移送は、同じ底上の射の頂点を保つ。
方針：底の図式の等式を消去する。
規約：移送の前後の可換性の証明は等式で連結する。
使われ方：Kerodon §5.6.2（Tag 026H）、終点の底の図式の表示の変更。 -/
lemma relativeFunctorVertex_transport {A E B : SSet.{u}} (p : E ⟶ B)
    {a b : A ⟶ B} (h : a = b) (f : A ⟶ E) (hf : f ≫ p = a) :
    (eqToHom (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p) h)).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p a f hf) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p b f (hf.trans h) := by
  subst b
  rfl

/-- 概要：底変換の順方向は通常の底上の射の第一射影への後合成に一致する。
方針：相対関手の頂点の内部 Hom 成分を比較する。
規約：p と f の充填性は不要。
使われ方：Kerodon Remark 5.6.2.18（Tag 0271）、底変換同型の頂点での計算。 -/
lemma relativeFunctorBaseChangeForward_vertex {A E B D : SSet.{u}}
    (p : E ⟶ B) (f : D ⟶ B) (a : A ⟶ D)
    (g : A ⟶ pullback p f) (hg : g ≫ pullback.snd p f = a) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorBaseChangeForward p f a).app _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex (pullback.snd p f) a g hg) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p (a ≫ f) (g ≫ pullback.fst p f) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hg]) := by
  apply Subtype.ext
  rfl

/-- 概要：底変換の逆方向は通常の射を引き戻しへ持ち上げる操作に一致する。
方針：順方向の単射性を使い、引き戻しの第一射影で確認する。
規約：底の図式 a を厳密に保つ持ち上げを用いる。
使われ方：Kerodon Remark 5.6.2.18（Tag 0271）、unstraightening の具体的な終点を回収する。 -/
lemma relativeFunctorBaseChangeBackward_vertex {A E B D : SSet.{u}}
    (p : E ⟶ B) (f : D ⟶ B) (a : A ⟶ D)
    (g : A ⟶ E) (hg : g ≫ p = a ≫ f) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorBaseChangeBackward p f a).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p (a ≫ f) g hg) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex (pullback.snd p f) a (pullback.lift g a hg)
        (pullback.lift_snd _ _ _) := by
  apply (ConcreteCategory.bijective_of_isIso ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorBaseChangeIso p f a).hom.app _)).1
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorBaseChangeBackward p f a) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorBaseChangeForward p f a).app _ _ = _
  rw [show _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorBaseChangeBackward p f a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorBaseChangeForward p f a =
      𝟙 _ from (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorBaseChangeIso p f a).inv_hom_id]
  rw [NatTrans.id_app, types_id_apply]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p (a ≫ f) g hg =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorBaseChangeForward p f a).app _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex (pullback.snd p f) a (pullback.lift g a hg) _)
  rw [relativeFunctorBaseChangeForward_vertex]
  simp only [pullback.lift_fst]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
