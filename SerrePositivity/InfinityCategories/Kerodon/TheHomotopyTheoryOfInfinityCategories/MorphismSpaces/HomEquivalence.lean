module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Homotopy
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Quasicategory

/-!
概要：局所 Kan な単体的圏の豊穣 Hom と coherent nerve の右写像空間の同値。
方針：旗の解像の右随伴との同型で比較射を同定し、その同値性を移す。
規約：対象の宇宙と Hom の宇宙は異なってよい。
使われ方：Kerodon Theorem 4.6.7.5（Tag 01LE）、Corollary 4.6.7.16（Tag 01LQ）、空間値 unstraightening の fiber 比較。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：豊穣 Hom から coherent nerve の右 pinched 写像空間への標準射は同値。
方針：旗の解像による表示の後で、Kan 複体の比較射の宇宙を持ち上げた射と比較する。
規約：全ての豊穣 Hom の Kan 性以外の充填仮定を追加しない。
使われ方：Kerodon Theorem 4.6.7.5（Tag 01LE）、coherent nerve が豊穣 Hom を回収する比較。 -/
lemma coherentHomComparison_isQCatEquivalence {C : Type v} [Category.{u} C]
    [SimplicialCategory C] [∀ X Y : C, KanComplex (SimplicialCategory.sHom X Y)] (X Y : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparison X Y) := by
  have he := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentPinchedFlagIso X Y)).isQCatEquivalence
  apply he.cancel_right
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparison X Y ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentPinchedFlagIso X Y).hom)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparison_flagIso]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionComparison_isQCatEquivalence
    (SimplicialCategory.sHom X Y)).ulift_of_kan

/-- 概要：coherent nerve の Hom 比較射は単体的ホモトピー同値。
方針：比較射の quasicategory の同値からホモトピー逆を取り出す。
規約：比較先は右 pinched 写像空間で、両側は Kan 複体。
使われ方：Kerodon Theorem 4.6.7.5（Tag 01LE）、fiber の値の回収に用いる写像空間の同値。 -/
lemma coherentHomComparison_isSimplicialHomotopyEquivalence {C : Type v} [Category.{u} C]
    [SimplicialCategory C] [∀ X Y : C, KanComplex (SimplicialCategory.sHom X Y)] (X Y : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparison X Y) :=
  (coherentHomComparison_isQCatEquivalence X Y).isSimplicialHomotopyEquivalence

/-- 概要：豊穣 Hom と coherent nerve の写像空間の明示的な同値データ。
方針：標準比較射の同値性から逆射と二つの可逆二胞体を選ぶ。
規約：順方向の射は標準の coherentHomComparison のまま。
使われ方：Kerodon Theorem 4.6.7.5（Tag 01LE）、単体的圏から作る ∞ 圏の写像空間の利用。 -/
noncomputable def coherentHomEquivalence {C : Type v} [Category.{u} C]
    [SimplicialCategory C] [∀ X Y : C, KanComplex (SimplicialCategory.sHom X Y)] (X Y : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence ((SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Y))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex Y)) :=
  (coherentHomComparison_isQCatEquivalence X Y).choose

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
