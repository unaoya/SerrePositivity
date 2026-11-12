module

public import SerrePositivity.KST.Spectra.PointedBasedPathComposition
public import SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeSymmetry

/-!
概要：非定数の境界区間への厳密な制限を、転置後の区間の同じ射影へ移す。
方針：相対 curry と交換同型の自然性を使い、二度の転置は同型の往復則で消す。
規約：Kan 性不要。使われ方：実際の境界修正区間と帰納構成の比較区間の同定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
namespace SerrePositivity.KST.Spectra.PointedMapping.VerticalPath

/-- 端点等式を付け替えた区間は、元の同じ一次単体を持つ。 -/
lemma changeEndpoints_edge_value {T E B : PointedSimplicialSet.{u}} {p : E ⟶ B}
    {f g f' g' : T ⟶ E} (P : VerticalPath p f g) (hf : f' = f) (hg : g' = g) :
    (P.changeEndpoints hf hg).edge.edge = P.edge.edge := by
  have h := path_eq_of_homotopy_h_eq (P.changeEndpoints hf hg) P
    (P.changeEndpoints_homotopy_h hf hg)
  exact congrArg SSet.yonedaEquiv h

/-- 端点表示の変更後も、転置した区間の同じパラメータ族を保つ。 -/
lemma changeEndpoints_basedTranspose_path {A U V : PointedSimplicialSet.{u}}
    {f g f' g' : A ⟶ (ihom U).obj V}
    (P : VerticalPath (PointedObject.toPoint ((ihom U).obj V)) f g)
    (hf : f' = f) (hg : g' = g) :
    (P.changeEndpoints hf hg).basedTranspose.path = P.basedTranspose.path := by
  cases hf
  cases hg
  have he : P.changeEndpoints rfl rfl = P := by cases P; rfl
  exact congrArg (fun Q ↦ Q.basedTranspose.path) he

/-- 評価した区間の制限が一致すれば、内部 Hom の非定数な区間族の制限も一致する。 -/
lemma path_restriction_eq_of_homotopy {A B E : PointedSimplicialSet.{u}}
    {f g : A ⟶ E} {f' g' : B ⟶ E}
    (P : VerticalPath (PointedObject.toPoint E) f g)
    (Q : VerticalPath (PointedObject.toPoint E) f' g') (j : B ⟶ A)
    (h : j.right ▷ (Δ[1] : SSet.{u}) ≫ P.homotopy.h = Q.homotopy.h) :
    P.path ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j E).right = Q.path := by
  apply (cancel_mono (PointedObject.basedHomι B E)).1
  change P.path ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre j E ≫ _ = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre_ι, ← Category.assoc]
  apply uncurry_injective
  rw [uncurry_pre_app, ← homotopy_h, ← homotopy_h]
  exact h

/-- 非定数な区間族の制限一致を評価すると、元のホモトピーの区間全体が一致する。 -/
lemma homotopy_restriction_eq_of_path {A B E : PointedSimplicialSet.{u}}
    {f g : A ⟶ E} {f' g' : B ⟶ E}
    (P : VerticalPath (PointedObject.toPoint E) f g)
    (Q : VerticalPath (PointedObject.toPoint E) f' g') (j : B ⟶ A)
    (h : P.path ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j E).right = Q.path) :
    j.right ▷ (Δ[1] : SSet.{u}) ≫ P.homotopy.h = Q.homotopy.h := by
  rw [homotopy_h, ← uncurry_pre_app, Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre_ι, ← Category.assoc]
  change uncurry ((P.path ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j E).right) ≫ PointedObject.basedHomι B E) = _
  rw [h, ← homotopy_h]

/-- 二度転置した同じ区間族は、元の区間族そのものに戻る。 -/
lemma basedTranspose_twice_path {A U V : PointedSimplicialSet.{u}}
    {f g : A ⟶ (ihom U).obj V}
    (P : VerticalPath (PointedObject.toPoint ((ihom U).obj V)) f g) :
    P.basedTranspose.basedTranspose.path = P.path := by
  change (P.path ≫ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A U V).hom.right) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso U A V).hom.right = P.path
  rw [_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.hom_eq_inv U A V]
  have h : (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A U V).hom.right ≫
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A U V).inv.right = 𝟙 _ :=
    congrArg Under.Hom.right (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A U V).hom_inv_id
  rw [Category.assoc, h]
  exact Category.comp_id P.path

/-- 元の非定数境界区間への制限は、転置後も同じ境界区間の転置へ厳密に射影される。 -/
lemma basedTranspose_restriction_path {A B U V : PointedSimplicialSet.{u}}
    {f g : A ⟶ (ihom U).obj V} {f' g' : B ⟶ (ihom U).obj V}
    (P : VerticalPath (PointedObject.toPoint ((ihom U).obj V)) f g)
    (Q : VerticalPath (PointedObject.toPoint ((ihom U).obj V)) f' g') (j : B ⟶ A)
    (h : P.path ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j ((ihom U).obj V)).right = Q.path) :
    P.basedTranspose.path ≫ (PointedObject.basedHomMap U (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j V)).right =
      Q.basedTranspose.path := by
  have hs := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeNaturality.natural_pre_left j U V
  simp only [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre] at hs
  have he := congrArg Under.Hom.right hs.symm
  change (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A U V).hom.right ≫
      (PointedObject.basedHomMap U (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j V)).right =
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j ((ihom U).obj V)).right ≫
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso B U V).hom.right at he
  change (P.path ≫ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A U V).hom.right) ≫ _ =
    Q.path ≫ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso B U V).hom.right
  rw [Category.assoc, he, ← Category.assoc, h]

end SerrePositivity.KST.Spectra.PointedMapping.VerticalPath
