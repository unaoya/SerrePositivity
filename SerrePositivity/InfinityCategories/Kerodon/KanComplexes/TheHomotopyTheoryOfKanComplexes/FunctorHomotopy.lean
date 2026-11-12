module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.SimplicialHomotopyEquivalence
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.PushoutProduct
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：関手単体集合の辺と実際の単体的ホモトピーの比較。
方針：内部 Hom の一次単体を uncurry し、両端を頂点表示で比較する。
規約：関手の同型を頂点ごとの同型だけへ弱めない。
使われ方：Kerodon §4.5.1（Tag 01DQ）、§4.8.4（Tag 06SQ） の関手の同値。

対応節は Kerodon 3.1（Tag 00SZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

/-- 概要：関手単体集合の頂点表示は単射。
方針：単位からの射の表示と閉構造の curry' の単射性を合成する。
規約：任意の単体集合間の射。
使われ方：Kerodon §4.5.1（Tag 01DQ） の辺とホモトピーの比較。 -/
lemma functorVertex_injective {X Y : SSet.{u}} :
    Function.Injective (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (X := X) (Y := Y)) := by
  intro f g h
  apply curry'_injective
  exact (SSet.unitHomEquiv _).injective h

/-- 概要：関手単体集合の辺の uncurry の先頭は辺の始点を表す。
方針：内部 Hom の単体への作用と先頭の端点を計算する。
規約：辺は任意の一次単体。
使われ方：Kerodon §4.5.1（Tag 01DQ） のホモトピーの先頭。 -/
lemma functorVertex_uncurry_zero {X Y : SSet.{u}} (s : ((ihom X).obj Y) _⦋1⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.ι₀ ≫ uncurry (SSet.yonedaEquiv.symm s)) =
      ((ihom X).obj Y).δ 1 s := by
  apply CategoryTheory.Functor.functorHom_ext
  intro d α
  have hα : α = (SimplexCategory.const d.unop ⦋0⦌ 0).op := Subsingleton.elim _ _
  subst α
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- 概要：関手単体集合の辺の uncurry の終端は辺の終点を表す。
方針：内部 Hom の単体への作用と終端の端点を計算する。
規約：辺は任意の一次単体。
使われ方：Kerodon §4.5.1（Tag 01DQ） のホモトピーの終端。 -/
lemma functorVertex_uncurry_one {X Y : SSet.{u}} (s : ((ihom X).obj Y) _⦋1⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.ι₁ ≫ uncurry (SSet.yonedaEquiv.symm s)) =
      ((ihom X).obj Y).δ 0 s := by
  apply CategoryTheory.Functor.functorHom_ext
  intro d α
  have hα : α = (SimplexCategory.const d.unop ⦋0⦌ 0).op := Subsingleton.elim _ _
  subst α
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- 概要：関手単体集合の二頂点を結ぶ辺は単体的ホモトピーを与える。
方針：辺を uncurry し、両端の頂点表示の単射性を用いる。
規約：逆辺の存在は仮定しない。
使われ方：Kerodon §4.5.1（Tag 01DQ） の関手のホモトピー。 -/
@[kerodon 00TU]
def simplicialHomotopyOfFunctorEdge {X Y : SSet.{u}} {f g : X ⟶ Y}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom X).obj Y))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g)) : SSet.Homotopy f g where
  h := uncurry (SSet.yonedaEquiv.symm e.edge)
  h₀ := functorVertex_injective ((functorVertex_uncurry_zero e.edge).trans e.src_eq)
  h₁ := functorVertex_injective ((functorVertex_uncurry_one e.edge).trans e.tgt_eq)
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    exact False.elim s.1.property

/-- 概要：関手単体集合の頂点の同型を表す辺を選ぶ。
方針：quasicategory の辺の類からホモトピー圏の Hom への全射性を使う。
規約：標的 Y の quasicategory 性だけを要求する。
使われ方：Kerodon §4.5.1（Tag 01DQ）、§4.8.4（Tag 06SQ） の実際のホモトピーの選択。 -/
noncomputable def FunctorIso.edge {X Y : SSet.{u}} [Quasicategory Y]
    {f g : X ⟶ Y} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) :
    SSet.Truncated.Edge (X := (truncation 2).obj ((ihom X).obj Y))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g) :=
  Classical.choose (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g) e.hom)

/-- 概要：選んだ辺の類は元の関手の同型の順方向の射。
方針：辺を選ぶ全射性の条件を読む。
規約：同型を表す代表の選択に依存する等式。
使われ方：Kerodon §4.5.1（Tag 01DQ） の可逆な関手の辺。 -/
lemma FunctorIso.edge_homMk {X Y : SSet.{u}} [Quasicategory Y]
    {f g : X ⟶ Y} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) :
    SSet.Truncated.HomotopyCategory.homMk (FunctorIso.edge e) = e.hom :=
  Classical.choose_spec
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g) e.hom)

/-- 概要：関手の同型を表す選んだ辺は可逆。
方針：辺の類が同型の順方向の射であることを使う。
規約：可逆性は A3b のホモトピー圏での可逆性。
使われ方：Kerodon §4.5.1（Tag 01DQ） の可逆な自然変換の代表。 -/
lemma FunctorIso.edge_isInvertible {X Y : SSet.{u}} [Quasicategory Y]
    {f g : X ⟶ Y} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (FunctorIso.edge e) := by
  change IsIso (SSet.Truncated.HomotopyCategory.homMk (FunctorIso.edge e))
  rw [FunctorIso.edge_homMk]
  infer_instance

/-- 概要：関手単体集合の頂点の同型は実際の単体的ホモトピーを与える。
方針：同型を表す辺を選んで uncurry する。
規約：同型から得るホモトピーの向きは f から g。
使われ方：Kerodon §4.5.1（Tag 01DQ）、§4.8.4（Tag 06SQ） の同値の具体的なホモトピー。 -/
noncomputable def FunctorIso.simplicialHomotopy {X Y : SSet.{u}} [Quasicategory Y]
    {f g : X ⟶ Y} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) : SSet.Homotopy f g :=
  simplicialHomotopyOfFunctorEdge (FunctorIso.edge e)

/-- 概要：quasicategory の同値は単体的ホモトピー同値。
方針：二つの可逆二胞体から実際の単体的ホモトピーを選ぶ。
規約：ホモトピー逆は同じ単体集合の逆射を使う。
使われ方：Kerodon §4.5.1（Tag 01DQ）、§4.8.4（Tag 06SQ） の同値のホモトピー的性質。 -/
lemma IsQCatEquivalence.isSimplicialHomotopyEquivalence {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {f : X ⟶ Y} (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence f := by
  obtain ⟨g, ⟨e⟩, ⟨e'⟩⟩ := hf
  exact ⟨g, ⟨FunctorIso.simplicialHomotopy e⟩, ⟨FunctorIso.simplicialHomotopy e'⟩⟩

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
