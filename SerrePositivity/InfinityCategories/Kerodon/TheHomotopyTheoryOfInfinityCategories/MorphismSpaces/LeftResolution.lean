module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ResolutionRetraction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.OppositeKanHomotopy

/-!
概要：左 Hom の fiber に現れる、反転で共役した旗の解像。
方針：X の反転に右随伴の解像を適用してもう一度反転し、二重反転を消して比較射を作る。
規約：解像は単体集合の通常の関手として構成し、coherent な豊穣作用は別に扱う。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、Corollary 5.6.0.6（Tag 028T）、反転した値の左 coslice fiber の座標。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：反転した入力の旗の解像を再び反転した左 Hom の解像模型。
方針：右随伴の解像を二つの反転で共役する。
規約：入力も出力も宇宙 u の単体集合。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、反転した空間値の左 fiber を同定する模型。 -/
noncomputable def coherentLeftResolution (X : SSet.{u}) : SSet.{u} :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionRightAdjoint.obj X.op).op

/-- 概要：左 Hom の解像模型は Kan 複体を Kan 複体へ写す。
方針：反転と旗の解像の右随伴による Kan 性の保存を使う。
規約：元の X に Kan 性を要求する。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、fiber の具体的な Kan 模型。 -/
instance coherentLeftResolution_kanComplex (X : SSet.{u}) [KanComplex X] :
    KanComplex (coherentLeftResolution X) :=
  inferInstanceAs (KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionRightAdjoint.obj X.op).op)

/-- 概要：左 Hom の解像模型を通常の単体集合の自己関手に束縛する。
方針：反転・右随伴・反転の三つの関手を合成する。
規約：対象での値は coherentLeftResolution と定義的に同じ。
使われ方：Kerodon §4.6.7（Tag 01LA）、fiber の座標比較の通常の射に関する自然性。 -/
noncomputable def coherentLeftResolutionFunctor : SSet.{u} ⥤ SSet.{u} :=
  SSet.opFunctor ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionRightAdjoint ⋙ SSet.opFunctor

/-- 概要：元の単体集合から左 Hom の解像への標準比較射。
方針：二重反転の逆同型に、反転した入力の標準比較射の反転を続ける。
規約：逆射を同値から選ばず実際の比較射を固定する。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、左 fiber の具体的な比較の入力。 -/
noncomputable def coherentLeftResolutionComparison (X : SSet.{u}) :
    X ⟶ coherentLeftResolution X :=
  (SSet.opFunctorCompOpFunctorIso.app X).inv ≫
    SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionComparison X.op)

/-- 概要：左 Hom の解像への標準比較は通常の単体集合の射に関して自然。
方針：右側の標準比較の自然変換を反転で挟み、二重反転の自然同型を合成する。
規約：全ての単体集合で自然性を述べる。
使われ方：Kerodon §4.6.7（Tag 01LA）、fiber の具体的な座標比較を図式へ束ねるための自然性。 -/
noncomputable def coherentLeftResolutionComparisonNat : 𝟭 SSet.{u} ⟶ coherentLeftResolutionFunctor :=
  SSet.opFunctorCompOpFunctorIso.inv ≫
    Functor.whiskerRight (Functor.whiskerLeft SSet.opFunctor _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionComparisonNat) SSet.opFunctor

/-- 概要：左 Hom の自然な比較の成分は固定した標準比較射。
方針：自然変換の合成と whiskering の成分を展開する。
規約：射の選択を変えない厳密な等式。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、具体的な fiber の比較に自然性を適用する。 -/
lemma coherentLeftResolutionComparisonNat_app (X : SSet.{u}) :
    coherentLeftResolutionComparisonNat.app X = coherentLeftResolutionComparison X := rfl

/-- 概要：Kan 複体から左 Hom の解像への標準比較は quasicategory の同値。
方針：反転した入力の右側の比較のホモトピー同値を反転し、二重反転の同型を合成する。
規約：構成した比較射そのものの同値性を述べる。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、反転した値の左 coslice fiber への具体的な同値射。 -/
lemma coherentLeftResolutionComparison_isQCatEquivalence (X : SSet.{u}) [KanComplex X] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (coherentLeftResolutionComparison X) := by
  let e : X ≅ X.op.op := (SSet.opFunctorCompOpFunctorIso.app X).symm
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso e).isQCatEquivalence.comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.oppositeKanHomotopyEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionComparison_isSimplicialHomotopyEquivalence X.op)).isQCatEquivalence

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
