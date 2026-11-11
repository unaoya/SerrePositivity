module

public import SerrePositivity.KST.LocalizingInvariants.ZeroArrowFamily
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroHomotopy

/-!
概要：二つの実関手の間に、全頂点で零射を表す一つの全図式ホモトピーを構成する。
方針：定値零関手の終対象性と始対象性から得た二胞体を合成し、実代表を取る。
規約：頂点ごとの辺の寄せ集めにせず、元の全図式と二端点を保持する。
使われ方：Sp-7 の成分内の零分母を、wide 部分複体の実収縮へ接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.ZeroArrowFamily
variable {K X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex X]

/-- 概要：元のパラメータ全体で定値な零関手。
方針：定値零関手の終対象性と始対象性から得た二胞体を合成し、実代表を取る。
規約：頂点ごとの辺の寄せ集めにせず、元の全図式と二端点を保持する。
使われ方：Sp-7 の成分内の零分母を、wide 部分複体の実収縮へ接続する。 -/
def constantZero : K ⟶ X := SSet.const (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.chosenZeroVertex X).vertex

omit [Quasicategory X] in
/-- 概要：定値零関手の各頂点は同じ零頂点。
方針：定値零関手の終対象性と始対象性から得た二胞体を合成し、実代表を取る。
規約：頂点ごとの辺の寄せ集めにせず、元の全図式と二端点を保持する。
使われ方：Sp-7 の成分内の零分母を、wide 部分複体の実収縮へ接続する。 -/
lemma constantZero_isZero (k : K _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex ((constantZero (K := K) (X := X)).app _ k) := by
  simpa [constantZero] using (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.chosenZeroVertex X).isZero

/-- 概要：元の二関手の間の、定値零関手を経る全二胞体。
方針：定値零関手の終対象性と始対象性から得た二胞体を合成し、実代表を取る。
規約：頂点ごとの辺の寄せ集めにせず、元の全図式と二端点を保持する。
使われ方：Sp-7 の成分内の零分母を、wide 部分複体の実収縮へ接続する。 -/
def nullHom (F G : K ⟶ X) : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F G :=
  ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isTerminalVertex_functorVertex_of_pointwise (constantZero (K := K) (X := X))
    (fun k => (constantZero_isZero k).2)).isTerminalHo.from
      (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F))) ≫
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isInitialVertex_functorVertex_of_pointwise (constantZero (K := K) (X := X))
      (fun k => (constantZero_isZero k).1)).isInitialHo.to
        (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)))

/-- 概要：全二胞体の同じ実代表。全単体と両端の関手を保持する。
方針：定値零関手の終対象性と始対象性から得た二胞体を合成し、実代表を取る。
規約：頂点ごとの辺の寄せ集めにせず、元の全図式と二端点を保持する。
使われ方：Sp-7 の成分内の零分母を、wide 部分複体の実収縮へ接続する。 -/
def nullHomotopy (F G : K ⟶ X) : SSet.Homotopy F G :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy (nullHom F G)

/-- 概要：同じ全図式ホモトピーの各頂点成分は、元の h 圏の零射を表す。
方針：定値零関手の終対象性と始対象性から得た二胞体を合成し、実代表を取る。
規約：頂点ごとの辺の寄せ集めにせず、元の全図式と二端点を保持する。
使われ方：Sp-7 の成分内の零分母を、wide 部分複体の実収縮へ接続する。 -/
lemma nullHomotopy_component [HasZeroMorphisms X.HomotopyCategory]
    (F G : K ⟶ X) (k : K _⦋0⦌) :
    (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge
      (nullHomotopy F G) k).toTruncated :
        (HomotopyCategory.mk (F.app _ k) : hoFunctor.obj X) ⟶
          HomotopyCategory.mk (G.app _ k)) = 0 := by
  rw [nullHomotopy, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy_component]
  unfold nullHom
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate_comp]
  have hz := (constantZero_isZero (X := X) k).isZeroHo
  exact (congrArg (fun a => a ≫ _) (hz.eq_zero_of_tgt _)).trans (zero_comp)

end SerrePositivity.KST.LocalizingInvariants.ZeroArrowFamily
