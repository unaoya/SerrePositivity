module

public import SerrePositivity.KST.Spectra.PointedRelativeTransposePaths
public import SerrePositivity.KST.Spectra.PointedVerticalChainCompression

/-!
概要：内部 Hom の制限への垂直区間を、指定部分全体を固定する転置後のホモトピーへ移す。
方針：元の交換と制限の厳密正方形を逆向きに使い、同じ区間を評価する。
規約：垂直鎖の圧縮には指定制限のホーン RLP だけを使う。使われ方：相対段座標の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
namespace SerrePositivity.KST.Spectra.PointedMapping
namespace VerticalPath

/-- 元の垂直区間の区間族そのものを、点への射影を持つ区間として扱う。 -/
def forgetProjection {T E B : PointedSimplicialSet.{u}} {p : E ⟶ B} {f g : T ⟶ E}
    (H : VerticalPath p f g) : VerticalPath (PointedObject.toPoint E) f g where
  path := H.path
  zero := H.zero
  one := H.one
  «over» := by
    apply (cancel_mono (PointedObject.basedHomι T PointedObject.point)).1
    apply uncurry_injective
    exact toUnit_unique _ _

/-- 元の区間族の制限が定数なら、評価したホモトピーは部分対象全体を固定する。 -/
lemma homotopy_restriction {A B E Z : PointedSimplicialSet.{u}} {p : E ⟶ Z} {f g : A ⟶ E}
    (H : VerticalPath p f g) (j : B ⟶ A)
    (hrel : H.path ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j E).right = SSet.const (familyVertex (j ≫ f))) :
    j.right ▷ (Δ[1] : SSet.{u}) ≫ H.homotopy.h =
      fst B.right (Δ[1] : SSet.{u}) ≫ j.right ≫ f.right := by
  rw [homotopy_h, ← uncurry_pre_app, Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre_ι, ← Category.assoc]
  change uncurry ((H.path ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j E).right) ≫ PointedObject.basedHomι B E) = _
  rw [hrel, uncurry_const_familyVertex]
  rfl

/-- 元の制限射影への垂直性は、転置した同じ区間の部分パラメータでの定数性となる。 -/
lemma transpose_path_restriction {A B U V : PointedSimplicialSet.{u}} {j : B ⟶ A}
    {f g : U ⟶ (ihom A).obj V} (H : VerticalPath (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j V) f g) :
    H.forgetProjection.basedTranspose.path ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j ((ihom U).obj V)).right =
      SSet.const (familyVertex (j ≫ transpose f)) := by
  have hs := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeSecondSource.natural_pre_right
    (C := PointedSimplicialSet.{u}) U j V
  simp only [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre] at hs
  have hs' := congrArg Under.Hom.right hs.symm
  change (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso U A V).hom.right ≫
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j ((ihom U).obj V)).right =
    (PointedObject.basedHomMap U (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j V)).right ≫
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso U B V).hom.right at hs'
  change (H.path ≫ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso U A V).hom.right) ≫ _ = _
  rw [Category.assoc, hs', ← Category.assoc, H.over, SSet.const_comp]
  exact congrArg SSet.const ((familyVertex_transpose (f ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j V)).symm.trans
    (congrArg familyVertex (transpose_pre_inner f j)))

/-- 元の垂直区間を、基点と指定部分全体を固定する実際の転置ホモトピーへ移す。 -/
lemma transpose_homotopy {A B U V : PointedSimplicialSet.{u}} {j : B ⟶ A}
    {f g : U ⟶ (ihom A).obj V} (H : VerticalPath (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j V) f g) :
    ∃ W : SSet.Homotopy (transpose f).right (transpose g).right,
      A.hom ▷ (Δ[1] : SSet.{u}) ≫ W.h =
        toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫ ((ihom U).obj V).hom ∧
      j.right ▷ (Δ[1] : SSet.{u}) ≫ W.h =
        fst B.right (Δ[1] : SSet.{u}) ≫ j.right ≫ (transpose f).right :=
  ⟨H.forgetProjection.basedTranspose.homotopy, H.forgetProjection.basedTranspose.homotopy_base,
    H.forgetProjection.basedTranspose.homotopy_restriction j H.transpose_path_restriction⟩

end VerticalPath

namespace VerticalChain

/-- 指定制限への垂直有限鎖を、指定部分全体を固定する逆向きの転置ホモトピーへ戻す。 -/
lemma transpose_reverse_homotopy {A B U V : PointedSimplicialSet.{u}} (j : B ⟶ A)
    [Mono j.right] [KanComplex V.right] {f g : U ⟶ (ihom A).obj V}
    (H : VerticalChain (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j V) f g) :
    ∃ W : SSet.Homotopy (transpose g).right (transpose f).right,
      A.hom ▷ (Δ[1] : SSet.{u}) ≫ W.h =
        toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫ ((ihom U).obj V).hom ∧
      j.right ▷ (Δ[1] : SSet.{u}) ≫ W.h =
        fst B.right (Δ[1] : SSet.{u}) ≫ j.right ≫ (transpose g).right := by
  obtain ⟨P⟩ := H.nonempty_reverse_path
    ((SSet.modelCategoryQuillen.fibration_iff _).1 (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre_fibration j V))
  exact P.transpose_homotopy

end VerticalChain
end SerrePositivity.KST.Spectra.PointedMapping
