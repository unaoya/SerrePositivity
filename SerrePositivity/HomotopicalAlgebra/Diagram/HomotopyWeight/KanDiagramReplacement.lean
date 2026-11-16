module

public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.ConeInvariance

/-!
# Kan 置換を介した重み付き錐の比較

概要：Hovey §5 の frame 比較の共通対象を関手的に Kan 置換する。
方針：実際のホーン小対象置換の単位の自然性と錐の Kan 図式不変性を使う。
規約：元の Kan 錐空間は変更せず、置換は比較の中間図式に使う。
使われ方：混合 Hom が Kan であるという追加仮定なしに両 frame の錐を比較する。
-/

@[expose] public section

noncomputable section

universe u v w

namespace SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.SerrePositivity.DiagramModel.WeightedCones _root_.SerrePositivity.SimplicialModel
open scoped _root_.SSet.modelCategoryQuillen

/-- 概要：ホーン小対象置換は anodyne 局所化同値を保つ（Hovey §5）。
方針：元の射と置換の単位の自然な四角形で同型性を移す。
規約：単体集合の完全なモデル構造は不要。
使われ方：混合 frame の比較を Kan 図式の比較へ移す。 -/
lemma kanReplacement_map_isIso {X Y : SSet.{u}} (f : X ⟶ Y)
    (hf : IsIso (AnodyneHomotopy.anodyneQ.map f)) :
    IsIso (AnodyneHomotopy.anodyneQ.map (AnodyneKanReplacement.functor.map f)) := by
  let Q := AnodyneHomotopy.anodyneQ.{u}
  have : IsIso (Q.map (AnodyneKanReplacement.unit.app X)) :=
    Localization.inverts Q SSet.anodyneExtensions _ (AnodyneKanReplacement.unit_anodyne X)
  have : IsIso (Q.map (AnodyneKanReplacement.unit.app Y)) :=
    Localization.inverts Q SSet.anodyneExtensions _ (AnodyneKanReplacement.unit_anodyne Y)
  have hn : f ≫ AnodyneKanReplacement.unit.app Y =
      AnodyneKanReplacement.unit.app X ≫ AnodyneKanReplacement.functor.map f :=
    AnodyneKanReplacement.unit.naturality f
  have hi : IsIso (Q.map (AnodyneKanReplacement.unit.app X) ≫
      Q.map (AnodyneKanReplacement.functor.map f)) := by
    rw [← Q.map_comp, ← hn, Q.map_comp]
    infer_instance
  exact (isIso_comp_left_iff _ _).mp hi

variable (K : Type u) [SmallCategory K]

/-- 概要：単体集合図式の関手的な各値の Kan 置換（Hovey §5）。
方針：ホーン小対象置換を図式に後合成する。
規約：全図式射を保持する。
使われ方：混合 Hom の比較の中間 Kan 図式。 -/
abbrev kanDiagram (F : K ⥤ SSet.{u}) : K ⥤ SSet.{u} := F ⋙ AnodyneKanReplacement.functor

/-- 概要：各値の Kan 置換への元の図式からの自然変換（Hovey §5）。
方針：ホーン小対象置換の単位を前合成する。
規約：各成分は実際の anodyne 射。
使われ方：元の Kan 錐空間を置換後と比較する。 -/
def kanDiagramUnit (F : K ⥤ SSet.{u}) : F ⟶ _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.kanDiagram K F :=
  Functor.whiskerLeft F AnodyneKanReplacement.unit

/-- 概要：図式射を各値の Kan 置換後の図式射へ送る（Hovey §5）。
方針：同じ置換関手を自然変換へ後合成する。
規約：元の比較の自然性を保持する。
使われ方：両側の frame からの共通 Kan 図式への比較。 -/
abbrev kanDiagramMap {F G : K ⥤ SSet.{u}} (f : F ⟶ G) : _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.kanDiagram K F ⟶ _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.kanDiagram K G :=
  Functor.whiskerRight f AnodyneKanReplacement.functor

/-- 概要：各値をホーン小対象置換した図式は Kan 値（Hovey §5）。
方針：終対象へのホーンの右持ち上げ性を使う。
規約：元の図式の値の Kan 性は不要。
使われ方：重み付き錐の不変性の入力条件。 -/
lemma kanDiagram_kanComplex (F : K ⥤ SSet.{u}) (k : K) : SSet.KanComplex ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.kanDiagram K F).obj k) :=
  (SSet.modelCategoryQuillen.fibration_iff _).mpr (AnodyneKanReplacement.terminal_rlp (F.obj k))

variable (W : K ⥤ SSet.{u}) (hW : (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.boundaries K).rlp.llp (initial.to W))

include hW

/-- 概要：元の Kan 値図式の錐は各値の Kan 置換後の錐と同型になる（Hovey §5.4）。
方針：置換単位の各値の anodyne 性と錐の Kan 図式不変性を使う。
規約：任意の anodyne を反転する関手の後で比較する。
使われ方：混合 frame の共通対象を置換して元の錐へ戻る。 -/
lemma coneSpace_kanDiagramUnit_isIso (F : K ⥤ SSet.{u})
    (hF : ∀ k, SSet.KanComplex (F.obj k)) {D : Type v} [Category.{w} D] (L : SSet.{u} ⥤ D)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) :
    IsIso (L.map ((coneSpace K W).map (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.kanDiagramUnit K F))) :=
  _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneSpace_map_isIso_of_pointwiseKan K W hW (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.kanDiagramUnit K F) hF (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.kanDiagram_kanComplex K F)
    (fun k => Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions _
      (AnodyneKanReplacement.unit_anodyne (F.obj k))) L hL

/-- 概要：各値の局所化同値の Kan 置換後の錐は同型になる（Hovey §5.4）。
方針：Kan 置換の同値保存と射影重みの錐の不変性を使う。
規約：元の比較の始域・終域には Kan 条件を要求しない。
使われ方：両側の frame の混合 Hom への二つの比較を反転する。 -/
lemma coneSpace_kanDiagramMap_isIso {F G : K ⥤ SSet.{u}} (f : F ⟶ G)
    (hf : ∀ k, IsIso (AnodyneHomotopy.anodyneQ.map (f.app k)))
    {D : Type v} [Category.{w} D] (L : SSet.{u} ⥤ D)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) :
    IsIso (L.map ((coneSpace K W).map (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.kanDiagramMap K f))) :=
  _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneSpace_map_isIso_of_pointwiseKan K W hW (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.kanDiagramMap K f)
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.kanDiagram_kanComplex K F) (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.kanDiagram_kanComplex K G)
    (fun k => _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.kanReplacement_map_isIso (f.app k) (hf k)) L hL

end SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight
