module

public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.HomotopyNatTrans
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpacePiZero
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.SimplicialHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic

/-!
概要：指定ホモトピーの垂直辺を制限から読み戻す。
方針：定値な一次単体の自然性を各次数で計算する。
規約：標的の充填性を仮定しない。
使われ方：Cat_∞ の錐の比較の頂点と図式の成分の計算。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

/-- 概要：ホモトピーの垂直辺を任意の形状の制限で計算する。
方針：定値一次単体の自然性と標準区間の恒等辺を使う。
規約：元の一単体の厳密な等式。
使われ方：全錐の比較の頂点と図式の成分の読み戻し。 -/
lemma homotopyVertexEdge_restrict {A B X : SSet.{u}} {f g : B ⟶ X}
    (G : SSet.Homotopy f g) (i : A ⟶ B) (x : A _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge G (i.app (Opposite.op ⦋0⦌) x)).edge =
      ((i ▷ (Δ[1] : SSet.{u})) ≫ G.h).app (Opposite.op ⦋1⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1, SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u}))) := by
  have hi : SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge := by
    apply SSet.stdSimplex.ext
    intro j
    fin_cases j <;> rfl
  have h := ConcreteCategory.congr_hom
    (i.naturality (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0).op) x
  change i.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (i.app (Opposite.op ⦋0⦌) x) 1 at h
  change G.h.app (Opposite.op ⦋1⦌)
    ((SSet.Truncated.Edge.id (X := (truncation 2).obj B) (i.app _ x)).edge,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge) =
    G.h.app (Opposite.op ⦋1⦌) (i.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1), SSet.yonedaEquiv (𝟙 Δ[1]))
  rw [h, hi, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one]
  rfl
/-- 概要：定値な制限を持つホモトピーの垂直辺は恒等辺の一次単体。
方針：制限の式と定値単体の自然性を使う。
規約：標的の quasicategory 性は不要。
使われ方：錐の頂点の比較を恒等射と同定する。 -/
lemma homotopyVertexEdge_constant {A B X : SSet.{u}} {f g : B ⟶ X}
    (G : SSet.Homotopy f g) (i : A ⟶ B) (a : A ⟶ X)
    (h : (i ▷ (Δ[1] : SSet.{u})) ≫ G.h = fst A Δ[1] ≫ a) (x : A _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge G (i.app (Opposite.op ⦋0⦌) x)).edge =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (a.app (Opposite.op ⦋0⦌) x) 1 := by
  rw [homotopyVertexEdge_restrict, h]
  exact ConcreteCategory.congr_hom
    (a.naturality (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0).op) x
/-- 概要：指定 prism に一致する制限の垂直辺はその prism の垂直辺。
方針：制限の式を評価して因子を交換する。
規約：指定された prism 自体を保持する。
使われ方：図式上の比較の辺を自然変換の指定成分と同定する。 -/
lemma homotopyVertexEdge_prism {A B X : SSet.{u}} {f g : B ⟶ X}
    (G : SSet.Homotopy f g) (i : A ⟶ B) (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ X)
    (h : (i ▷ (Δ[1] : SSet.{u})) ≫ G.h = (β_ A (Δ[1] : SSet.{u})).hom ≫ H)
    (x : A _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge G (i.app (Opposite.op ⦋0⦌) x)).edge =
      H.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1) := by
  rw [homotopyVertexEdge_restrict, h]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
