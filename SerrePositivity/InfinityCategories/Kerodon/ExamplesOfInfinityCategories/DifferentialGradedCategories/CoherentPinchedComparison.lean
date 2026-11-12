module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CoherentVertices

/-!
# 比較写像が誘導する右 pinched Hom の射

概要：標準 coherent 頂点の間の pinched Hom から dg nerve の pinched Hom への実際の射を作る。
方針：比較写像を各単体に適用し、端点の等式と自然性から固定条件を得る。
規約：両方の写像空間は対象と係数環を合わせた宇宙 max u v に置く。
使われ方：HA 1.3.1.17、Kerodon 2.5.9（Tag 00SC） の比較写像の充満忠実性。

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

/-- 概要：二つの dg 対象に対応する coherent 頂点の右 pinched Hom。
方針：既存の一般の pinched Hom に標準の coherent 頂点を指定する。
規約：同じ型の対象を固定し、頂点の同一視は構成の後に行う。
使われ方：Kerodon 2.5.9（Tag 00SC） の余単体的立方体模型による比較の始域。 -/
def coherentPinchedHom (x y : D) : SSet.{max u v} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentVertex (R := R) x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentVertex (R := R) y)

/-- 概要：coherent pinched 単体を同じ二対象の dg pinched 単体へ送る。
方針：比較写像の自然性と標準頂点の像の等式で先頭面と最終頂点を固定する。
規約：端点の cast を元の単体の val に残さない。
使われ方：HA 1.3.1.17 の写像空間への比較の各次数の写像。 -/
def coherentPinchedSimplex {x y : D} {n : ℕ}
    (s : (coherentPinchedHom (R := R) x y) _⦋n⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R D x y) _⦋n⦌ where
  val := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparison.app _ s.val
  source := by
    calc
      _ = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparison.app (Opposite.op ⦋n⦌)
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanCoherentNerve (R := R) (D := D)).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.front n).op s.val) :=
        (ConcreteCategory.congr_hom
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparison.naturality (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.front n).op) s.val).symm
      _ = _ := by rw [s.source, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparison_vertex]
  target := by
    calc
      _ = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparison.app (Opposite.op ⦋0⦌)
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanCoherentNerve (R := R) (D := D)).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.lastVertex n).op s.val) :=
        (ConcreteCategory.congr_hom
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparison.naturality (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.lastVertex n).op) s.val).symm
      _ = _ := by rw [s.target, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparison_vertex]

/-- 概要：比較写像は固定した二対象の右 pinched Hom の射を誘導する。
方針：各次数の像をまとめ、最終点を固定した延長写像での自然性を使う。
規約：全ての面・退化との可換性を持つ実際の単体集合の射。
使われ方：Kerodon 2.5.9（Tag 00SC） の A3e の判定に接続する比較射。 -/
def coherentPinchedComparison (x y : D) :
    coherentPinchedHom (R := R) x y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R D x y where
  app _ := ↾coherentPinchedSimplex
  naturality := by
    intro m n α
    apply ConcreteCategory.hom_ext
    intro s
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex.ext
    exact ConcreteCategory.congr_hom
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparison.naturality (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend α.unop).op) s.val

/-- 概要：pinched Hom の比較射の台の単体は実際の dg 比較単体である。
方針：各次数の写像の定義を評価する。
規約：端点の固定条件は命題であり、台の単体を変えない。
使われ方：HA 1.3.1.17 の比較射の成分の立方体評価への同定。 -/
lemma coherentPinchedComparison_val {x y : D} {n : ℕ}
    (s : (coherentPinchedHom (R := R) x y) _⦋n⦌) :
    ((coherentPinchedComparison x y).app _ s).val = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentSimplex s.val := rfl

/-- 概要：coherent pinched Hom の比較射の全成分は最終点を加えた集合の立方体評価である。
方針：N4 の線形成分の回収の HEq と比較単体の成分の HEq を合成する。
規約：N4 の f 座標で述べ、標準 DK 座標との符号変更を混同しない。
使われ方：Kerodon 2.5.9（Tag 00SC） の余単体的立方体の比較射との照合。 -/
lemma coherentPinchedComparison_component_heq {x y : D} {n : ℕ}
    (s : (coherentPinchedHom (R := R) x y) _⦋n⦌)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData ((coherentPinchedComparison x y).app _ s)).component
      J k hJ hk)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeComponent s.val
        (show (ULift.up (J.min' hJ).castSucc : ULift.{u} (Fin (n + 2))) <
          ULift.up (Fin.last (n + 1)) from Fin.castSucc_lt_last _)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentVertexInterior (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast J)
          (J.min' hJ).castSucc (Fin.last (n + 1)))) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData_component_heq
    ((coherentPinchedComparison x y).app _ s) J k hJ hk).trans
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentSimplexData_hom_heq s.val _ _ _ _ _ _ _ _

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
