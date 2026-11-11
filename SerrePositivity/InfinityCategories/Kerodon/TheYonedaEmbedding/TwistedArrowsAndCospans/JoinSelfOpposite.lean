module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinTensorPoint
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinReverseBoundary

/-!
概要：反転した単体集合と元の単体集合の join の自己反転同型。
方針：join の因子を交換する反転同型と二重反転の消去を合成する。
規約：任意の単体集合 A を扱い、Stable の証明済みの join の同型を参照する。
使われ方：Kerodon Remark 8.1.1.7（Tag 03JL）、edgewise 重みの双対性の自然性。

対応節は Kerodon 8.1（Tag 03JB）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

/-- 概要：Aop ⋆ A の反転は自然に Aop ⋆ A と同型。
方針：join の反転で因子を交換し、右因子の二重反転を戻す。
規約：始域は join 全体の反転。
使われ方：Kerodon Remark 8.1.1.7（Tag 03JL）、重みの反転同型の一般形。 -/
noncomputable def joinSelfOppositeIso (A : SSet.{u}) : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A.op A).op ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A.op A :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinReverseIso A.op A ≪≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinIso (Iso.refl A.op) (SSet.opFunctorCompOpFunctorIso.app A)

/-- 概要：自己反転同型は A に関して自然。
方針：join の反転の自然性と二重反転同型の自然性を組み合わせる。
規約：左因子の射は f の反転、右因子は f。
使われ方：Kerodon Remark 8.1.1.7（Tag 03JL）、edgewise の単体作用との整合性。 -/
lemma joinSelfOpposite_naturality {A B : SSet.{u}} (f : A ⟶ B) :
    SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.opFunctor.map f) f) ≫ (joinSelfOppositeIso B).hom =
      (joinSelfOppositeIso A).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.opFunctor.map f) f := by
  change SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.opFunctor.map f) f) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinReverseIso B.op B).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 B.op) (SSet.opFunctorCompOpFunctorIso.app B).hom =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinReverseIso A.op A).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 A.op) (SSet.opFunctorCompOpFunctorIso.app A).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.opFunctor.map f) f
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinReverse_naturality, Category.assoc,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp]
  simp only [Category.comp_id, Category.id_comp]
  erw [SSet.opFunctorCompOpFunctorIso.hom.naturality f]

/-- 概要：自己反転同型の逆も A に関して自然。
方針：同型の自然性を同型の合成による相殺で移す。
規約：双対写像の定義には逆方向を使う。
使われ方：Kerodon Remark 8.1.1.7（Tag 03JL）、反転した射の始域の回収。 -/
lemma joinSelfOpposite_inv_naturality {A B : SSet.{u}} (f : A ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.opFunctor.map f) f ≫ (joinSelfOppositeIso B).inv =
      (joinSelfOppositeIso A).inv ≫ SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.opFunctor.map f) f) := by
  apply (cancel_mono (joinSelfOppositeIso B).hom).1
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
    joinSelfOpposite_naturality, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- 概要：逆自己反転に沿って右包含は左包含の反転に移る。
方針：join の因子の逆同型で右包含を移し、反転した join の包含の式を使う。
規約：二重反転同型の逆を始域へ合成する。
使われ方：Kerodon Remark 8.1.1.7（Tag 03JL）、左右の端点射影の交換。 -/
lemma joinSelfOpposite_inv_inr (A : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A.op A ≫ (joinSelfOppositeIso A).inv =
      (SSet.opFunctorCompOpFunctorIso.app A).inv ≫ SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A.op A) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A.op A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 A.op) (SSet.opFunctorCompOpFunctorIso.app A).inv ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinReverseIso A.op A).inv = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap_assoc]
  erw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinReverse_inr_inv A.op A]

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
