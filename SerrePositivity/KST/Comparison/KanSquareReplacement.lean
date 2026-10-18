module

public import SerrePositivity.KST.Comparison.HomotopyPullbackPasting

/-!
# 四角形の縦射の関手的な Kan 分解

概要：四角形の二つの縦射を同じ関手的分解で置き換え、比較を保存・反映する。
方針：arrow 圏の射への中間対象の関手と単位の自然性を使う。
規約：Segal 1974 Proposition 1.6 の骨格の比較の補助。
使われ方：中央の Kan 性を仮定しない横の貼り合わせ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits
open SerrePositivity.SimplicialModel

/--
概要：縦射の Kan 分解の中間対象の間の上辺。
方針：四角形を arrow 圏の射として中間対象の関手へ送る。
規約：同じ縦射には厳密に同じ中間対象を使う。
使われ方：二つの四角形を整合したまま置換する。
-/
def kanSquareTop {P X Y B : SSet.{u}} {a : P ⟶ X} {b : P ⟶ Y}
    {f : X ⟶ B} {g : Y ⟶ B} (sq : CommSq a b f g) :
    AnodyneKanReplacement.factorization.Z.obj (Arrow.mk b) ⟶
      AnodyneKanReplacement.factorization.Z.obj (Arrow.mk f) :=
  AnodyneKanReplacement.factorization.Z.map 
    (Arrow.homMk (f := Arrow.mk b) (g := Arrow.mk f) a g sq.w)

/--
概要：縦射を関手的に置換した可換四角形。
方針：分解の射影の自然性を使う。
規約：下辺は元の下辺を保つ。
使われ方：Kan fibration の四角形への還元。
-/
theorem kanReplacementSquare {P X Y B : SSet.{u}} {a : P ⟶ X} {b : P ⟶ Y}
    {f : X ⟶ B} {g : Y ⟶ B} (sq : CommSq a b f g) :
    CommSq (kanSquareTop sq)
      (AnodyneKanReplacement.factorization.p.app (Arrow.mk b))
      (AnodyneKanReplacement.factorization.p.app (Arrow.mk f)) g :=
  ⟨AnodyneKanReplacement.factorization.p.naturality 
    (Arrow.homMk (f := Arrow.mk b) (g := Arrow.mk f) a g sq.w)⟩

/--
概要：分解の単位は四角形の上辺と可換。
方針：分解の単位の arrow 圏での自然性を使う。
規約：元の上辺から置換した上辺へ向かう等式。
使われ方：四頂点の比較と外周の自然性。
-/
@[reassoc] theorem kanSquareTop_unit {P X Y B : SSet.{u}} {a : P ⟶ X} {b : P ⟶ Y}
    {f : X ⟶ B} {g : Y ⟶ B} (sq : CommSq a b f g) :
    a ≫ AnodyneKanReplacement.factorization.i.app (Arrow.mk f) =
      AnodyneKanReplacement.factorization.i.app (Arrow.mk b) ≫ kanSquareTop sq :=
  AnodyneKanReplacement.factorization.i.naturality 
    (Arrow.homMk (f := Arrow.mk b) (g := Arrow.mk f) a g sq.w)

/--
概要：縦射の Kan 分解は四角形のホモトピー引き戻し性を保存・反映する。
方針：上側の二頂点の単位の anodyne 性と四頂点の不変性を使う。
規約：下側の対象には Kan 性を課さない。
使われ方：一般の四角形の横の貼り合わせ。
-/
theorem kanReplacementSquare_homotopyPullback_iff
    {P X Y B : SSet.{u}} {a : P ⟶ X} {b : P ⟶ Y}
    {f : X ⟶ B} {g : Y ⟶ B} (sq : CommSq a b f g) :
    IsHomotopyPullback sq ↔ IsHomotopyPullback (kanReplacementSquare sq) := by
  apply isHomotopyPullback_iff_of_localized_isIso sq (kanReplacementSquare sq)
    (AnodyneKanReplacement.factorization.i.app (Arrow.mk b))
    (AnodyneKanReplacement.factorization.i.app (Arrow.mk f)) (𝟙 _) (𝟙 _)
    (kanSquareTop_unit sq) ?_ ?_ (by simp)
    (Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions _
      (AnodyneKanReplacement.factorization.factorizationData b).hi)
    (Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions _
      (AnodyneKanReplacement.factorization.factorizationData f).hi)
    (by infer_instance) (by infer_instance)
  · rw [Category.comp_id]
    exact (AnodyneKanReplacement.factorization.fac_app (f := Arrow.mk b)).symm
  · rw [Category.comp_id]
    exact (AnodyneKanReplacement.factorization.fac_app (f := Arrow.mk f)).symm

end SerrePositivity.KST.Comparison
