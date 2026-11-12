module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.SquareDuality
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentOppositeIso

/-!
概要：native な余錐の値域の同型による移送と coherent nerve の反対からの帰還。
方針：coslice の後合成の同型で始対象性を移し、coherent nerve の同型と二重反転を合成する。
規約：既存の JoinCocone・IsColimitCone をそのまま使う。Kan 性は不要。
使われ方：HTT 4.2.4.1、極限側の成果を余極限へ双対化する際の値域の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 概要：native な余錐を値域の射で後合成する。
方針：coslice の後合成を零単体に適用する。
規約：図式も同じ射で後合成したものに移る。
使われ方：coherent nerve の反対の同型で余錐を元の値域へ戻す。 -/
def coherentCoconePost {K X Y : SSet.{u}} {p : K ⟶ X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (q : X ⟶ Y) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (p ≫ q) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp p q).app (Opposite.op ⦋0⦌) c

/-- 概要：余錐の後合成の元の図式は元の余錐の射への後合成。
方針：coslice の後合成の定義を使う。
規約：join からの実際の射の等式。
使われ方：余錐の脚と図式の固定条件の追跡。 -/
lemma coherentCoconePost_val {K X Y : SSet.{u}} {p : K ⟶ X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (q : X ⟶ Y) : (coherentCoconePost c q).val = c.val ≫ q := rfl

/-- 概要：余錐の後合成の頂点は元の頂点の像。
方針：右包含で制限し、Yoneda 表示の後合成の式を使う。
規約：頂点は命題的な等式で比較する。
使われ方：余極限対象を元の通常の余錐の頂点と照合する。 -/
lemma coherentCoconePost_vertex {K X Y : SSet.{u}} {p : K ⟶ X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (q : X ⟶ Y) : (coherentCoconePost c q).vertex = q.app _ c.vertex := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex_eq, coherentCoconePost_val, ← Category.assoc, SSet.yonedaEquiv_comp]
  rfl

/-- 概要：値域の同型への後合成は native な余極限性を保存し反映する。
方針：coslice の後合成の同型による始対象性の不変性を使う。
規約：図式や値域に quasicategory 性を要求しない。
使われ方：反対の coherent nerve 上の余極限を元の値域へ移す。 -/
lemma coherentCoconePost_isColimit_iff {K X Y : SSet.{u}} {p : K ⟶ X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (q : X ⟶ Y) [IsIso q] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (coherentCoconePost c q) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isInitialVertex_iff_of_isIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp p q) c

/-- 概要：固定図式の等式で native な余錐を元の射を変えずに移送する。
方針：図式の等式で部分型を移送する。
規約：添字と値域は共通。Kan 性は不要。
使われ方：双対化した図式を標準の strict 図式に正規化する。 -/
def coherentCoconeOfDiagramEq {K X : SSet.{u}} {p q : K ⟶ X}
    (h : p = q) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone q := h ▸ c

/-- 概要：固定図式の等式で余錐を移送しても join からの実際の射は変わらない。
方針：等式を除いて恒等式へ帰着する。
規約：固定条件の証明の選択には依存しない。
使われ方：正規化した余錐の脚を元の余錐と照合する。 -/
lemma coherentCoconeOfDiagramEq_val {K X : SSet.{u}} {p q : K ⟶ X}
    (h : p = q) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) : (coherentCoconeOfDiagramEq h c).val = c.val := by
  subst q
  rfl

/-- 概要：固定図式の等式による余錐の移送は頂点を保持する。
方針：等式を除いて同じ右包含の評価へ戻す。
規約：頂点の命題的な等式。
使われ方：正規化した余錐の余極限対象の保持。 -/
lemma coherentCoconeOfDiagramEq_vertex {K X : SSet.{u}} {p q : K ⟶ X}
    (h : p = q) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) : (coherentCoconeOfDiagramEq h c).vertex = c.vertex := by
  subst q
  rfl

/-- 概要：固定図式の等式による余錐の移送は native な余極限性を保持する。
方針：等式を除いて同じ coslice の始対象性へ戻す。
規約：値域の quasicategory 性は要求しない。
使われ方：双対化で証明した余極限性を標準の図式上に公開する。 -/
lemma coherentCoconeOfDiagramEq_isColimit_iff {K X : SSet.{u}} {p q : K ⟶ X}
    (h : p = q) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (coherentCoconeOfDiagramEq h c) := by
  subst q
  rfl

/-- 概要：反対の単体的圏の coherent nerve の反転から元の coherent nerve へ戻る標準同型。
方針：coherent nerve の反対の同型の逆を反転し、二重反転を消す。
規約：対象と Hom の二宇宙を区別する。Kan 性は不要。
使われ方：通常の余錐の反対の錐から native な余錐を構成する。 -/
def coherentOppositeReturnIso (C : Type v) [Category.{u} C] [SimplicialCategory C] :
    (SimplicialNerve Cᵒᵖ).op ≅ SimplicialNerve C :=
  SSet.opFunctor.mapIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentNerveOppositeIso C).symm ≪≫
    SSet.opFunctorCompOpFunctorIso.app (SimplicialNerve C)

/-- 概要：反対の coherent nerve からの帰還は元の対象の頂点を保持する。
方針：反対の標準逆射の頂点の計算と二重反転の同型を使う。
規約：反対の頂点は opObjEquiv で明示する。
使われ方：native な余錐の頂点が元の通常の頂点に一致することの確認。 -/
lemma coherentOppositeReturnIso_hom_vertex {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (x : C) : (coherentOppositeReturnIso C).hom.app _
        (SSet.opObjEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (Opposite.op x))) = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x := by
  change (SSet.opFunctorCompOpFunctorIso.app (SimplicialNerve C)).hom.app _
    ((SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentNerveOppositeInverse C)).app _
      (SSet.opObjEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (Opposite.op x)))) = _
  rw [SSet.opFunctor_map, Equiv.apply_symm_apply, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentNerveOppositeInverse_vertex]
  rfl

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
