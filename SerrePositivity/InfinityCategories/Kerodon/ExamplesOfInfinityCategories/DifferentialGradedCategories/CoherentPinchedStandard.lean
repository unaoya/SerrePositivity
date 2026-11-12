module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CoherentPinchedComparison
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CoherentVertexEquiv

/-!
# coherent pinched Hom の比較を標準 DK 座標で表す

概要：実際の pinched Hom の比較射を標準 DK Hom への射に直し、その全成分を明示する。
方針：N4 の回収と標準座標の符号変換を、既存の自然同型に沿って合成する。
規約：始域・終域を max u v の宇宙で比較する。
使われ方：HA 1.3.1.17、Kerodon 2.5.9（Tag 00SC） の余単体的立方体模型からのホモトピー逆の構成。

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

/-- 概要：持ち上げた標準 DK Hom は dg nerve の右 pinched Hom と自然同型である。
方針：N4 座標への符号変換の逆と、線形解から pinched 単体への同型を合成する。
規約：Mathlib Γ への同型を経由せず、明示的な標準座標を使う。
使われ方：Kerodon 2.5.9（Tag 00SC） の比較射の終域を単体的加群で表す。 -/
def standardHomPinchedIso (x y : D) :
    SSet.uliftFunctor.{v, u}.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) x y) ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R D x y :=
  SSet.uliftFunctor.{v, u}.mapIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.homSpaceStandardIso (R := R) x y).symm ≪≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.homSpaceLiftIso (R := R) x y

/-- 概要：coherent pinched Hom の比較射を持ち上げた標準 DK Hom への射として取る。
方針：実際の dg pinched Hom の比較射の後に標準座標への自然同型の逆を合成する。
規約：全ての面・退化で自然な単体集合の射である。
使われ方：HA 1.3.1.17 のホモトピー逆を構成する際の座標表示。 -/
def coherentPinchedStandardComparison (x y : D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentPinchedHom (R := R) x y ⟶
      SSet.uliftFunctor.{v, u}.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) x y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentPinchedComparison x y ≫ (standardHomPinchedIso x y).inv

/-- 概要：標準座標での比較の各単体は N4 の成分回収に符号変換を施した値である。
方針：同型の逆と射の合成の定義を評価する。
規約：宇宙の持ち上げは down で忘れてから標準単体を表示する。
使われ方：Kerodon 2.5.9（Tag 00SC） の立方体の基本鎖の評価との全成分の照合。 -/
lemma coherentPinchedStandardComparison_app {x y : D} {n : ℕ}
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentPinchedHom (R := R) x y) _⦋n⦌) :
    ((coherentPinchedStandardComparison x y).app _ s).down =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardSimplexEquiv x y n
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentPinchedComparison x y).app _ s)) := rfl

/-- 概要：標準座標の比較成分は N4 回収成分に次数符号を掛けた値である。
方針：標準単体の符号変換の成分を計算する。
規約：符号は J の濃度から得る degreeSign (|J|−1)。
使われ方：HA 1.3.1.17 の比較射と標準 DK Hom のホモトピー逆との合成の検証。 -/
lemma coherentPinchedStandardComparison_component {x y : D} {n : ℕ}
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentPinchedHom (R := R) x y) _⦋n⦌)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    ((coherentPinchedStandardComparison x y).app _ s).down.val.component J k hJ hk =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.degreeSign (J.card - 1) •
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentPinchedComparison x y).app _ s)).component
          J k hJ hk := rfl

/-- 概要：標準座標の比較の後に pinched Hom の同型を戻すと元の比較射になる。
方針：自然同型の逆射と順射を相殺する。
規約：次数ごとの値だけでなく単体集合の射の等式。
使われ方：Kerodon 2.5.9（Tag 00SC） の標準座標でのホモトピー逆を実際の比較射へ移す。 -/
lemma coherentPinchedStandardComparison_comp (x y : D) :
    coherentPinchedStandardComparison (R := R) x y ≫ (standardHomPinchedIso x y).hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentPinchedComparison x y := by
  simp only [coherentPinchedStandardComparison, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
