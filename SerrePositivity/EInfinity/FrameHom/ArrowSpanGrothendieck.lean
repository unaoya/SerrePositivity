module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ArrowSpanComma
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CommaGrothendieck
public import SerrePositivity.EInfinity.FrameHom.FrameElementSpans

/-!
# 三本矢の全図式と元の frame の比較の Grothendieck 表示

概要：Low 命題 3.7 の三本矢と元の全単体の比較を同じ全図式で表示する。
方針：両脚の comma と右脚に沿う Grothendieck 構成の明示的な順逆を合成する。
規約：元の frame の単体・両脚・中間射を変更しない。
使われ方：分解側の余終性と右脚の全図式の不変性を組み合わせる比較。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.EInfinity.FrameHom.ArrowSpan

open CategoryTheory


variable {C : Type u} [Category.{v} C] (L R : MorphismProperty C) (X Y : C)

/-- 概要：元の右脚の全 slice 上の中間射の図式（Low 命題 3.7）。
方針：左脚の slice の射影に対する costructured arrow を右脚で送る。
規約：全ての指定右脚と全可換三角形を含む。
使われ方：三本矢の全図式の Grothendieck 構成。 -/
abbrev rightDiagram : R.Under ⊤ Y ⥤ Cat.{v, max u v} :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CommaGrothendieck.diagram (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ArrowSpanComma.leftSliceForget L X) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ArrowSpanComma.rightSliceForget R Y)

/-- 概要：元の三本矢を同じ右脚の全図式へ送る（Low 命題 3.7）。
方針：元の両脚の comma 表示と明示的な Grothendieck の逆関手を合成する。
規約：対象や射の新しい代表を選ばない。
使われ方：元の全単体の比較の厳密な因子分解。 -/
def toGrothendieck : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Object L R X Y ⥤ Grothendieck (rightDiagram L R X Y) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ArrowSpanComma.toComma L R X Y ⋙ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CommaGrothendieck.fromComma _ _

/-- 概要：右脚の全図式から元の三本矢へ戻す（Low 命題 3.7）。
方針：同じ底と fiber を元の両脚・中間射へ戻す。
規約：元の対象と三射をそのまま回収する。
使われ方：三本矢への元の比較射の回収。 -/
def fromGrothendieck : Grothendieck (rightDiagram L R X Y) ⥤ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Object L R X Y :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CommaGrothendieck.toComma _ _ ⋙ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ArrowSpanComma.fromComma L R X Y

/-- 概要：全図式を経由して元の三本矢を厳密に回収（Low 命題 3.7）。
方針：全ての元の対象・射・可換条件を評価する。
規約：全対象・全射の関手の等式。
使われ方：frame の元の比較射との厳密な一致。 -/
lemma toGrothendieck_fromGrothendieck :
    toGrothendieck L R X Y ⋙ fromGrothendieck L R X Y = 𝟭 _ := rfl

/-- 概要：右脚の全図式は元の三本矢の圏と同値（Low 命題 3.7）。
方針：元の二つの明示的な圏同値を合成する。
規約：順関手は元の底と fiber から三射を取り出す fromGrothendieck。
使われ方：三本矢の全図式のホモトピー型の表示。 -/
def grothendieckEquivalence : Grothendieck (rightDiagram L R X Y) ≌ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Object L R X Y :=
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CommaGrothendieck.equivalence _ _).trans (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ArrowSpanComma.commaEquivalence L R X Y).symm

variable {X Y} {Z : C} (A : SimplexCategory ⥤ C)
  (p : A ⟶ (Functor.const SimplexCategory).obj X) (hp : ∀ n, L (p.app n))
  (j : Y ⟶ Z) (hj : R j)

/-- 概要：元の frame の全単体の比較を右脚の全図式へ送る（Low 命題 3.7）。
方針：既存の全単体の比較の後に元の明示的な表示関手を置く。
規約：元の単体と全単体作用素を保持する。
使われ方：右射の反転性を元の同じ比較射で証明する。 -/
def frameGrothendieckFunctor : (((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj Z).Elements)ᵒᵖ ⥤
    Grothendieck (rightDiagram L R X Y) :=
  frameElementSpanFunctor L R A p hp j hj ⋙ toGrothendieck L R X Y

/-- 概要：同じ全図式を経由すると元の frame の全単体の比較（Low 命題 3.7）。
方針：元の表示関手の厳密な逆則を全単体に適用する。
規約：別の比較射へのホモトピーによる置き換えは使わない。
使われ方：元の特殊な三本矢への右射との一致。 -/
lemma frameGrothendieckFunctor_fac :
    frameGrothendieckFunctor L R A p hp j hj ⋙ fromGrothendieck L R X Y =
      frameElementSpanFunctor L R A p hp j hj := by
  unfold frameGrothendieckFunctor
  rw [CategoryTheory.Functor.assoc, toGrothendieck_fromGrothendieck,
    CategoryTheory.Functor.comp_id]

/-- 概要：全単体の元の右脚は全図式の底としてそのまま残る（Low 命題 3.7）。
方針：元の表示関手の対象成分を評価する。
規約：元の指定した j を保持する。
使われ方：固定右端から全右脚への包含の照合。 -/
lemma frameGrothendieckFunctor_base (s : (((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj Z).Elements)ᵒᵖ) :
    ((frameGrothendieckFunctor L R A p hp j hj).obj s).base =
      MorphismProperty.Under.mk ⊤ j hj := rfl

/-- 概要：全単体の元の中間射は同じ fiber の構造射（Low 命題 3.7）。
方針：元の表示関手の fiber を評価する。
規約：元の単体の射を変更しない。
使われ方：元の Map^h と全図式の中間 Hom の照合。 -/
lemma frameGrothendieckFunctor_middle (s : (((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj Z).Elements)ᵒᵖ) :
    ((frameGrothendieckFunctor L R A p hp j hj).obj s).fiber.hom = s.unop.val := rfl

/-- 概要：右脚の全 slice には元の恒等射の対象がある（Low 命題 3.7）。
方針：指定射の類の恒等射の証明を使う。
規約：元の対象 Y の恒等射そのもの。
使われ方：全右脚上のホモトピー不変な Hom 図式の基点。 -/
def rightSliceInitial [R.ContainsIdentities] (Y : C) : R.Under ⊤ Y :=
  MorphismProperty.Under.mk ⊤ (𝟙 Y) (R.id_mem Y)

/-- 概要：元の恒等右脚は全右脚の slice の始対象（Low 命題 3.7）。
方針：元の各右脚を唯一の可換三角形に使う。
規約：全ての指定右脚を扱う。
使われ方：右変数の全図式の基点への比較。 -/
def rightSliceInitial_isInitial [R.ContainsIdentities] (Y : C) :
    CategoryTheory.Limits.IsInitial (rightSliceInitial R Y) :=
  CategoryTheory.Limits.IsInitial.ofUniqueHom
    (fun t => MorphismProperty.Under.homMk t.hom (Category.id_comp t.hom)) (by
      intro t f
      apply MorphismProperty.Under.Hom.ext
      exact (Category.id_comp f.right).symm.trans (Under.w f.hom))

end SerrePositivity.EInfinity.FrameHom.ArrowSpan
