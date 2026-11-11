module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.MaximumCubeEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.HomNaturality

/-!
# 標準 Hom から coherent pinched Hom への射

概要：F1 の最大頂点による豊穣関手を使い、標準 Hom の各単体を coherent pinched 単体に送る。
方針：標準の coherent 頂点を同定し、確定済みの F1 の全単調写像での自然性を使う。
規約：この射を定義しただけでは比較射のホモトピー逆とは主張しない。
使われ方：HA 1.3.1.17、Kerodon 2.5.9（Tag 00SC） の写像空間の比較の逆向きの候補。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]

/-- 概要：F1 の標準頂点と dg 比較で使う標準頂点は等しい。
方針：coherent 零単体の唯一の対象からの再構成を使う。
規約：二つの定値関手の実装の差を等式で吸収する。
使われ方：Kerodon 2.5.9（Tag 00SC） の一般の豊穣 Hom の射を本比較の固定端点に移す。 -/
lemma coherentNerveVertex_eq_vertex (x : ClosedCategory R D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentVertex (R := R) (D := D) x :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentVertex_reconstruct (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x)).symm

/-- 概要：標準 Hom の単体から最大頂点を通じて coherent pinched 単体を作る。
方針：F1 の豊穣関手の先頭面・最終頂点の等式に端点の同定を合成する。
規約：台の coherent 単体は一般の F1 の構成そのもの。
使われ方：HA 1.3.1.17 の逆向きの比較射の各次数の値。 -/
def standardCoherentPinchedSimplex {x y : ClosedCategory R D} {n : ℕ}
    (σ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex R (D := D) x y n) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentPinchedHom (R := R) (D := D) x y) _⦋n⦌ where
  val := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonSimplex (X := x) (Y := y) σ
  source := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparisonSimplex_source (X := x) (Y := y) σ).trans
    (congrArg (fun z ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant z n) (coherentNerveVertex_eq_vertex x))
  target := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparisonSimplex_target (X := x) (Y := y) σ).trans
    (coherentNerveVertex_eq_vertex y)

/-- 概要：持ち上げた標準 Hom から coherent pinched Hom への自然な射。
方針：標準 Hom の各単体を最大頂点の構成に送り、F1 の自然性で面・退化と可換にする。
規約：対象を閉零射の圏の対象として指定し、宇宙 max u v で比較する。
使われ方：Kerodon 2.5.9（Tag 00SC） の実際の比較射のホモトピー逆の構成。 -/
def standardHomToCoherentPinched (x y : ClosedCategory R D) :
    SSet.uliftFunctor.{v, u}.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) (D := D) x y) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentPinchedHom (R := R) (D := D) x y where
  app _ := ↾fun σ ↦ standardCoherentPinchedSimplex σ.down
  naturality := by
    intro m n α
    apply ConcreteCategory.hom_ext
    intro σ
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex.ext
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparisonSimplex_naturality (X := x) (Y := y) α.unop σ.down).symm

/-- 概要：標準 Hom の射の台の単体は F1 の最大頂点による比較単体である。
方針：各次数の射の定義を評価する。
規約：端点の固定の証明は台の豊穣関手の値を変えない。
使われ方：HA 1.3.1.17 の比較射との合成を立方体評価で計算する入口。 -/
lemma standardHomToCoherentPinched_val {x y : ClosedCategory R D} {n : ℕ}
    (σ : (SSet.uliftFunctor.{v, u}.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) (D := D) x y)) _⦋n⦌) :
    ((standardHomToCoherentPinched x y).app _ σ).val =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonSimplex (X := x) (Y := y) σ.down := rfl

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
