module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.CompositionSquareTriangles
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.StdSimplexProductMap

/-!
概要：正方形を上側の三角形へ畳み、恒等合成の補完と同一視する。
方針：頂点の単調写像を用い、二つの二単体への制限で図式を照合する。
規約：畳み込みは元の正方形の上側をそのまま保持する。
使われ方：B1 の比較の両合成を、正方形全体の変形で検証する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories

/-- 概要：正方形の右下の頂点を最初の頂点へ畳む単調写像。
方針：上辺の二頂点は 1,2、下辺は 0 へ送る。
規約：座標は正方形の横・縦の順。
使われ方：上側の三角形への retraction。 -/
def squareUpperFoldOrder : Fin 2 × Fin 2 →o Fin 3 where
  toFun p := if p.2 = 0 then 0 else if p.1 = 0 then 1 else 2
  monotone' := by decide

/-- 概要：正方形を上側の三角形へ畳む射。
方針：頂点の単調写像を標準単体の直積の射にする。
規約：上側の三角形上では恒等。
使われ方：合成三角形の正方形への補完の具体表示。 -/
def squareUpperFold : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ Δ[2] :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexProductMap squareUpperFoldOrder

/-- 概要：上側の三角形を畳むと恒等射。
方針：標準二単体で有限計算する。
規約：厳密な retraction。
使われ方：元の上側の二単体を保持する。 -/
lemma squareUpperFold_upper : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle.{u} 0 ≫ squareUpperFold = 𝟙 _ := by
  apply SSet.yonedaEquiv.injective
  decide

/-- 概要：下側の三角形を畳むと対角辺の恒等合成になる。
方針：三頂点を 0,0,2 へ送ることを有限計算する。
規約：最初の辺を退化させる。
使われ方：正方形の補完の退化三角形との照合。 -/
lemma squareUpperFold_lower : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle.{u} 1 ≫ squareUpperFold =
    stdSimplex.σ (0 : Fin 2) ≫ stdSimplex.δ (1 : Fin 3) := by
  apply SSet.yonedaEquiv.injective
  decide

/-- 概要：畳み込みの上辺は三角形の後辺。
方針：一次単体で有限計算する。
規約：射の厳密な等式。
使われ方：相対三角形比較の上辺の固定。 -/
lemma squareUpperFold_top : (SSet.ι₁ : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) ≫
    squareUpperFold = stdSimplex.δ (0 : Fin 3) := by
  apply SSet.yonedaEquiv.injective
  decide

/-- 概要：畳み込みの左辺は三角形の前辺。
方針：一次単体で有限計算する。
規約：射の厳密な等式。
使われ方：相対三角形比較の左辺の固定。 -/
lemma squareUpperFold_left : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] : SSet.{u}) ≫
    squareUpperFold = stdSimplex.δ (2 : Fin 3) := by
  apply SSet.yonedaEquiv.injective
  decide

/-- 概要：畳み込みの右辺は三角形の対角辺。
方針：一次単体で有限計算する。
規約：射の厳密な等式。
使われ方：相対三角形比較の対角の path の回収。 -/
lemma squareUpperFold_right : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] : SSet.{u}) ≫
    squareUpperFold = stdSimplex.δ (1 : Fin 3) := by
  apply SSet.yonedaEquiv.injective
  decide

/-- 概要：畳み込みの下辺は最初の頂点に定値。
方針：一次単体で有限計算する。
規約：零単体を経由する因子分解を保持する。
使われ方：補完した正方形の比較中の下辺の固定。 -/
lemma squareUpperFold_bottom : (SSet.ι₀ : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) ≫
    squareUpperFold = stdSimplex.isTerminalObj₀.from Δ[1] ≫
      stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3) := by
  apply SSet.yonedaEquiv.injective
  decide

/-- 概要：恒等合成の二単体は指定辺の退化そのもの。
方針：Yoneda で idComp の零番目の退化を読む。
規約：指定ホモトピーの代表を変更しない。
使われ方：正方形の補完を一つの畳み込みとして表示する。 -/
lemma functorIdentityCompositionDiagram_eq_degeneracy {A X : SSet.{u}} {U W : A ⟶ X}
    (d : SSet.Homotopy U W) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorIdentityCompositionDiagram d = stdSimplex.σ (0 : Fin 2) ≫ curry d.h := by
  apply SSet.yonedaEquiv.injective
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorIdentityCompositionDiagram, Equiv.apply_symm_apply, stdSimplex.yonedaEquiv_σ_comp]
  rfl

/-- 概要：三角形を正方形へ補完する構成は畳み込みによる前合成。
方針：正方形の pushout の二つの二単体で照合する。
規約：射の厳密な等式で、quasicategory 性は不要。
使われ方：三角形のホモトピーを正方形全体に移す。 -/
lemma functorSquareOfCompositionTriangle_eq_fold {A X : SSet.{u}} {U V W : A ⟶ X}
    {l : SSet.Homotopy U V} {r : SSet.Homotopy V W} {d : SSet.Homotopy U W}
    (T : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle l r d) :
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorSquareOfCompositionTriangle T).diagram = squareUpperFold ≫ T.diagram := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.hom_ext
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.desc _ _ _ = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.inl_desc, ← Category.assoc, squareUpperFold_upper, Category.id_comp]
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.desc _ _ _ = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.inr_desc, ← Category.assoc, squareUpperFold_lower, Category.assoc,
      T.face_one, functorIdentityCompositionDiagram_eq_degeneracy]

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
