module

public import SerrePositivity.KST.Comparison.DiagramKanReplacement
public import SerrePositivity.KST.Comparison.SpanCylinderFunctor
public import SerrePositivity.KST.Comparison.HomotopyPullbackThreeInputs

/-!
# 図式の Kan 分解による四角形の比較

概要：図式の射の関手的な Kan 分解は、成分の四角形と円筒への頂点の四角形の性質を保つ。
方針：自然変換の可換四角形を因子化し、単位の各成分と円筒での可逆性を使う。
規約：Mather 1976 Lemma 21 の fibration への還元。厳密な引き戻しへの還元とは区別する。
使われ方：Segal 1974 Lemma 1.7 を縦射が Kan fibration の場合へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe w v u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits
open SerrePositivity.SimplicialModel

/--
概要：自然変換と元の圏の射が作る可換四角形。
方針：自然性の等式を四角形の向きに合わせる。
規約：上辺と下辺は自然変換の成分、縦辺は関手が射に誘導する写像。
使われ方：頂点の円筒への包含の自然性の四角形。
-/
theorem naturalitySquare {D : Type v} [Category.{w} D] {V T : D ⥤ SSet.{u}} (ν : V ⟶ T)
    {F G : D} (α : F ⟶ G) : CommSq (ν.app F) (V.map α) (T.map α) (ν.app G) :=
  ⟨(ν.naturality α).symm⟩

/--
概要：射の因子化の前半が二関手の下で局所化同型なら、自然性の四角形を因子化の後半へ置換できる。
方針：元の四角形と置換後の四角形を四頂点の局所化同型で比較する。
規約：因子化や二つの関手は任意であり、中心の貼り合わせ定理は仮定しない。
使われ方：図式の Kan 分解の単位で四角形を移す。
-/
theorem naturalitySquare_factorization_iff {D : Type v} [Category.{w} D]
    {V T : D ⥤ SSet.{u}} (ν : V ⟶ T) {F H G : D}
    (α : F ⟶ G) (i : F ⟶ H) (p : H ⟶ G) (h : i ≫ p = α)
    (hV : IsIso (AnodyneHomotopy.anodyneQ.map (V.map i)))
    (hT : IsIso (AnodyneHomotopy.anodyneQ.map (T.map i))) :
    IsHomotopyPullback (naturalitySquare ν α) ↔ IsHomotopyPullback (naturalitySquare ν p) := by
  apply isHomotopyPullback_iff_of_localized_isIso
    (naturalitySquare ν α) (naturalitySquare ν p) (V.map i) (T.map i) (𝟙 _) (𝟙 _)
  · exact (ν.naturality i).symm
  · simp only [Category.comp_id, ← V.map_comp, h]
  · simp only [Category.comp_id, ← T.map_comp, h]
  · simp
  · exact hV
  · exact hT
  · infer_instance
  · infer_instance

/--
概要：図式の一つの射は、定義域と終域の評価関手の間の自然変換となる。
方針：各図式でその射を評価し、図式の自然変換の自然性を使う。
規約：添字の圏は任意。
使われ方：span の二つの面のホモトピー引き戻し性の置換。
-/
def diagramArrow {D : Type v} [Category.{w} D] {d e : D} (θ : d ⟶ e) :
    (evaluation D SSet.{u}).obj d ⟶ (evaluation D SSet.{u}).obj e where
  app F := F.map θ
  naturality {_ _} α := (α.naturality θ).symm

/--
概要：図式の射の Kan 分解は、添字の任意の射に対応する四角形のホモトピー引き戻し性を保つ。
方針：二つの評価関手と、成分ごとに anodyne な単位を因子化の比較へ適用する。
規約：span の場合、二つの面を同時に置換できる。
使われ方：元の homotopy-cartesian な span を縦射が Kan fibration の場合へ移す。
-/
theorem diagramKan_arrowSquare_iff {D : Type v} [Category.{w} D]
    {F G : D ⥤ SSet.{u}} (α : F ⟶ G) {d e : D} (θ : d ⟶ e) :
    IsHomotopyPullback (naturalitySquare (diagramArrow θ) α) ↔
      IsHomotopyPullback (naturalitySquare (diagramArrow θ) (diagramKanProjection α)) := by
  apply naturalitySquare_factorization_iff (diagramArrow θ) α
    (diagramKanUnit α) (diagramKanProjection α) (diagramKan_fac α)
  · exact Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions _
      (diagramKanUnit_anodyne α d)
  · exact Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions _
      (diagramKanUnit_anodyne α e)

/--
概要：span の Kan 分解の単位が円筒に誘導する射は局所化同型である。
方針：単位の各成分の anodyne 性と、円筒の模型の不変性を使う。
規約：射影の成分が Kan fibration であることは別に証明済み。
使われ方：円筒への頂点の四角形の置換。
-/
theorem spanCylinderKanUnit_localized_isIso {F G : WalkingSpan ⥤ SSet.{u}} (α : F ⟶ G) :
    IsIso (AnodyneHomotopy.anodyneQ.map (spanCylinderFunctor.map (diagramKanUnit α))) :=
  spanCylinderFunctor_map_localized_isIso _ (fun d =>
    Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions _
      (diagramKanUnit_anodyne α d))

/--
概要：span の Kan 分解は、任意の頂点から円筒への四角形のホモトピー引き戻し性を保つ。
方針：評価関手と円筒の関手について、単位を局所化同型とした因子化の比較を使う。
規約：三つの頂点全てに適用できる。一般の貼り合わせの本体は別の証明項目。
使われ方：Segal Lemma 1.7 の結論を縦射が Kan fibration の場合へ還元する。
-/
theorem spanCylinderKan_vertexSquare_iff {F G : WalkingSpan ⥤ SSet.{u}}
    (α : F ⟶ G) (d : WalkingSpan) :
    IsHomotopyPullback (naturalitySquare (spanCylinderVertex d) α) ↔
      IsHomotopyPullback (naturalitySquare (spanCylinderVertex d) (diagramKanProjection α)) := by
  apply naturalitySquare_factorization_iff (spanCylinderVertex d) α
    (diagramKanUnit α) (diagramKanProjection α) (diagramKan_fac α)
  · exact Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions _
      (diagramKanUnit_anodyne α d)
  · exact spanCylinderKanUnit_localized_isIso α

end SerrePositivity.KST.Comparison
