module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinLifting
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：通常の join の左因子の連結な余極限の保存。
方針：固定した右因子の under 圏への join と slice の随伴を作る。
規約：既存の join の直接定義は維持する。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） のセルと骨格の貼り合わせ。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

/-- 概要：右因子 K を固定した join を K の under 圏への関手にする。
方針：右包含と joinMap の自然性を使う。
規約：可変因子は左側。
使われ方：Kerodon §4.3.5（Tag 017V）・4.6.2（Tag 01HM） の slice との随伴。 -/
def joinLeftUnderFunctor (K : SSet.{u}) : SSet.{u} ⥤ Under K where
  obj A := Under.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A K)
  map {A B} f := Under.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 K)) (by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A K ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 K) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr B K
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.id_comp])
  map_id A := by
    apply Under.UnderMorphism.ext
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_id A K
  map_comp f g := by
    apply Under.UnderMorphism.ext
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (f ≫ g) (𝟙 K) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 K) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap g (𝟙 K)
    simpa only [Category.id_comp] using _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp f g (𝟙 K) (𝟙 K)

/-- 概要：K の under 圏の対象をその slice へ送る関手。
方針：各単体の錐を under 圏の射の右成分で後合成する。
規約：固定された図式の等式は under 圏の可換条件を使う。
使われ方：Kerodon §4.3.5（Tag 017V）・4.6.2（Tag 01HM） の join の余極限。 -/
def sliceOverUnderFunctor (K : SSet.{u}) : Under K ⥤ SSet.{u} where
  obj p := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p.hom
  map f :=
    { app n := ↾fun σ ↦ ⟨σ.val ≫ f.right, by
        rw [← Category.assoc, σ.property, Under.w]⟩
      naturality _ _ α := by
        apply ConcreteCategory.hom_ext
        intro σ
        apply Subtype.ext
        exact Category.assoc _ _ _ }
  map_id p := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro σ
    apply Subtype.ext
    exact Category.comp_id _
  map_comp f g := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro σ
    apply Subtype.ext
    exact (Category.assoc _ _ _).symm

/-- 概要：固定した右因子を持つ join と slice は under 圏を通じて随伴する。
方針：任意の単体集合に対する slice の普遍性を自然な Hom の同値にする。
規約：quasicategory 性は不要。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） の join の連結な余極限の保存。 -/
@[kerodon 018A]
def joinLeftUnderAdjunction (K : SSet.{u}) : joinLeftUnderFunctor K ⊣ sliceOverUnderFunctor K :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun A p ↦
        { toFun f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverCurry f.right (Under.w f)
          invFun f := Under.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry f) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_fixed f)
          left_inv f := by
            apply Under.UnderMorphism.ext
            exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_curry f.right (Under.w f)
          right_inv f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverCurry_uncurry f }
      homEquiv_naturality_left_symm := by
        intro A B p f g
        apply Under.UnderMorphism.ext
        exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_precomp g f
      homEquiv_naturality_right := by
        intro A p q f g
        apply SSet.hom_ext
        intro n
        apply ConcreteCategory.hom_ext
        intro a
        apply Subtype.ext
        change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.yonedaEquiv.symm a) (𝟙 K) ≫ (f.right ≫ g.right) =
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.yonedaEquiv.symm a) (𝟙 K) ≫ f.right) ≫ g.right
        exact (Category.assoc _ _ _).symm }

/-- 概要：under 圏への join 関手は左随伴。
方針：構成した join と slice の随伴を使う。
規約：固定した右因子 K は任意。
使われ方：Kerodon §4.6.2（Tag 01HM） の余極限保存。 -/
instance joinLeftUnderFunctor_isLeftAdjoint (K : SSet.{u}) :
    (joinLeftUnderFunctor K).IsLeftAdjoint := (joinLeftUnderAdjunction K).isLeftAdjoint

/-- 概要：右因子 K を固定した通常の join 関手。
方針：under 圏への join の関手から固定部分を忘れる。
規約：対象は既存の join、射は既存の joinMap と定義的に一致する。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） の自然な比較。 -/
def joinLeftFunctor (K : SSet.{u}) : SSet.{u} ⥤ SSet.{u} :=
  joinLeftUnderFunctor K ⋙ Under.forget K

/-- 概要：固定した右因子との通常の join は連結な余極限を保つ。
方針：左随伴の余極限保存と under 圏の忘却関手の連結な余極限保存を合成する。
規約：形 J は連結。quasicategory 性は不要。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） の無限のセル分解。 -/
instance joinLeftFunctor_preservesConnectedColimits (K : SSet.{u})
    (J : Type*) [Category* J] [IsConnected J] :
    PreservesColimitsOfShape J (joinLeftFunctor K) := by
  unfold joinLeftFunctor
  infer_instance

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "1.2.8.2"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinLeftUnderAdjunction
