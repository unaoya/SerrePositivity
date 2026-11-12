module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.LeftStrictTransport
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.RelativeFunctorRestrictionFibration

/-!
概要：薄い通常の圏上の strict transport の構造射の全ホーン持ち上げ性。
方針：Under.map の対象の単射性と nerve の単射性を示し、相対関手の制限に適用する。
規約：薄い圏には有限順序を含むが、対象の反対称性や有限性は要求しない。
使われ方：Kerodon §5.3.1（Tag 035D）、Theorem 5.3.5.7（Tag 037Q）、有限順序上の scaffold 比較の相対充填。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：薄い圏の undercategory は薄い圏。
方針：under の射を元の圏の射へ忘れ、Hom の一意性を忠実な忘却で反映する。
規約：under の対象の型の subsingleton 性は主張しない。
使われ方：Kerodon §5.3.1（Tag 035D）、有限順序の undercategory の nerve の射列の比較。 -/
instance under_isThin_of_thin
    {C : Type u} [Category.{u} C] [Quiver.IsThin C] (c : C) : Quiver.IsThin (Under c) :=
  fun _ _ ↦ ⟨fun g h ↦ StructuredArrow.hom_ext g h (Subsingleton.elim _ _)⟩

/-- 概要：薄い圏の射による undercategory の前合成は対象に単射。
方針：射の標的を忘れて対象を回収し、構造射の一意性で under の対象を復元する。
規約：底の対象が同型なら等しいとは仮定しない。
使われ方：Kerodon §5.3.1（Tag 035D）、有限順序の末尾の undercategory の包含。 -/
lemma underMap_obj_injective_of_thin
    {C : Type u} [Category.{u} C] [Quiver.IsThin C] {c d : C} (f : c ⟶ d) :
    Function.Injective (Under.map f).obj := by
  rintro ⟨⟨⟨⟩⟩, a, g⟩ ⟨⟨⟨⟩⟩, b, h⟩ he
  have hab : a = b := congrArg (fun z : Under c ↦ z.right) he
  subst b
  exact congrArg Under.mk (Subsingleton.elim g h)

/-- 概要：薄い圏の射による undercategory の nerve の前合成は単射。
方針：各次数の射列を対象の単射性と Hom の一意性で回収する。
規約：元の射 f は任意でよい。
使われ方：Kerodon §5.3.1（Tag 035D）、相対関手空間の制限の単射条件。 -/
instance nerveUnderMap_mono_of_thin
    {C : Type u} [Category.{u} C] [Quiver.IsThin C] {c d : C} (f : c ⟶ d) :
    Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.nerveUnderMap f) := by
  rw [NatTrans.mono_iff_mono_app]
  intro k
  rw [mono_iff_injective]
  intro σ τ h
  change σ ⋙ Under.map f = τ ⋙ Under.map f at h
  refine CategoryTheory.Functor.ext (fun i ↦ ?_) (fun _ _ _ ↦ Subsingleton.elim _ _)
  exact underMap_obj_injective_of_thin f (congrArg (fun ξ ↦ ξ.obj i) h)

/-- 概要：薄い圏上の left fibration の strict transport の構造射は全ホーンを持ち上げる。
方針：under の nerve の単射による相対関手空間の制限として判定する。
規約：Kan 値と Fibration の意味はホーンの右持ち上げ性に限る。
使われ方：Kerodon §5.3.1（Tag 035D）、1 単体上の strict transport の比較のパラメータの持ち上げ。 -/
lemma leftStrictTransportMap_fibration_of_thin
    {C : Type u} [Category.{u} C] [Quiver.IsThin C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] {c d : C} (f : c ⟶ d) :
    Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportMap p f) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre_fibration p (nerveMap (Under.forget c)) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.nerveUnderMap f)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
