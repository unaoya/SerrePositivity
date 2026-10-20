module

public import SerrePositivity.EInfinity.HomotopyWeight.KanDiagramReplacement

/-!
# 共通図式を介した Kan 錐の比較と自然性

概要：Hovey §5.4 の共通分解を、Kan 図式の重み付き錐の自然な比較へ移す。
方針：共通図式への二つの射を Kan 置換し、同型の積で比較する。
規約：共通図式に Kan 性を要求せず、元の錐を保持する。
使われ方：両 frame の錐の比較の自然性と元の比較射の追跡。
-/

@[expose] public section

noncomputable section

universe u v w

namespace SerrePositivity.EInfinity.HomotopyWeight

open CategoryTheory Limits
open SerrePositivity.DiagramModel.WeightedCones SerrePositivity.SimplicialModel

variable (K : Type u) [SmallCategory K] (W : K ⥤ SSet.{u})
  (hW : (boundaries K).rlp.llp (initial.to W))
  {D : Type v} [Category.{w} D] (L : SSet.{u} ⥤ D)
  (hL : SSet.anodyneExtensions.IsInvertedBy L)

/-- 概要：共通図式への射と Kan 置換単位を合成した実際の錐の比較射（Hovey §5）。
方針：元の射を Kan 置換し、元の始域からの単位に後合成する。
規約：元の重みと射を使う。
使われ方：左右の錐の同型を特徴づける可換三角形。 -/
def coneComparisonArrow {F H : K ⥤ SSet.{u}} (f : F ⟶ H) :
    L.obj ((coneSpace K W).obj F) ⟶ L.obj ((coneSpace K W).obj (kanDiagram K H)) :=
  L.map ((coneSpace K W).map (kanDiagramUnit K F)) ≫
    L.map ((coneSpace K W).map (kanDiagramMap K f))

include hW hL

/-- 概要：共通図式への各値の局所化同値は Kan 錐を同型にする（Hovey §5.4）。
方針：Kan 単位と Kan 置換後の射の二つの同型を合成する。
規約：共通図式の値には Kan 条件を置かない。
使われ方：左右の frame の共通図式への比較の反転。 -/
lemma coneComparisonArrow_isIso {F H : K ⥤ SSet.{u}} (f : F ⟶ H)
    (hF : ∀ k, SSet.KanComplex (F.obj k))
    (hf : ∀ k, IsIso (AnodyneHomotopy.anodyneQ.map (f.app k))) :
    IsIso (coneComparisonArrow K W L f) := by
  have := coneSpace_kanDiagramUnit_isIso K W hW F hF L hL
  have := coneSpace_kanDiagramMap_isIso K W hW f hf L hL
  dsimp only [coneComparisonArrow]
  infer_instance

/-- 概要：共通図式への二つの比較は元の Kan 錐を同型にする（Hovey §5.4）。
方針：左比較と右比較の逆を合成する。
規約：任意の anodyne 反転先で同じ射の比較を取る。
使われ方：両側 frame の錐の比較。 -/
def kanConeComparisonIso {F G H : K ⥤ SSet.{u}} (f : F ⟶ H) (g : G ⟶ H)
    (hF : ∀ k, SSet.KanComplex (F.obj k)) (hG : ∀ k, SSet.KanComplex (G.obj k))
    (hf : ∀ k, IsIso (AnodyneHomotopy.anodyneQ.map (f.app k)))
    (hg : ∀ k, IsIso (AnodyneHomotopy.anodyneQ.map (g.app k))) :
    L.obj ((coneSpace K W).obj F) ≅ L.obj ((coneSpace K W).obj G) := by
  have := coneComparisonArrow_isIso K W hW L hL f hF hf
  have := coneComparisonArrow_isIso K W hW L hL g hG hg
  exact asIso (coneComparisonArrow K W L f) ≪≫ (asIso (coneComparisonArrow K W L g)).symm

/-- 概要：錐の比較同型は元の二つの比較射を結ぶ（Hovey §5.4）。
方針：右比較の逆と順方向の合成を消す。
規約：元の共通図式への射を厳密に保持する。
使われ方：比較後の零単体の類の同定と自然性。 -/
lemma kanConeComparisonIso_fac {F G H : K ⥤ SSet.{u}} (f : F ⟶ H) (g : G ⟶ H)
    (hF : ∀ k, SSet.KanComplex (F.obj k)) (hG : ∀ k, SSet.KanComplex (G.obj k))
    (hf : ∀ k, IsIso (AnodyneHomotopy.anodyneQ.map (f.app k)))
    (hg : ∀ k, IsIso (AnodyneHomotopy.anodyneQ.map (g.app k))) :
    (kanConeComparisonIso K W hW L hL f g hF hG hf hg).hom ≫
      coneComparisonArrow K W L g = coneComparisonArrow K W L f := by
  have := coneComparisonArrow_isIso K W hW L hL g hG hg
  simp [kanConeComparisonIso]

omit hW hL in
/-- 概要：共通図式への錐の比較射は可換四角形に自然（Hovey §5.4）。
方針：Kan 置換単位の自然性と関手の合成保存を使う。
規約：四角形は元の図式の射の厳密な等式で指定する。
使われ方：両 frame の錐の比較を図式の射に自然にする。 -/
lemma coneComparisonArrow_naturality {F F' H H' : K ⥤ SSet.{u}}
    (f : F ⟶ H) (f' : F' ⟶ H') (a : F ⟶ F') (c : H ⟶ H') (h : a ≫ f' = f ≫ c) :
    L.map ((coneSpace K W).map a) ≫ coneComparisonArrow K W L f' =
      coneComparisonArrow K W L f ≫ L.map ((coneSpace K W).map (kanDiagramMap K c)) := by
  let T := coneSpace K W ⋙ L
  change T.map a ≫ (T.map (kanDiagramUnit K F') ≫ T.map (kanDiagramMap K f')) =
    (T.map (kanDiagramUnit K F) ≫ T.map (kanDiagramMap K f)) ≫ T.map (kanDiagramMap K c)
  simp only [← T.map_comp]
  congr 1
  have hn : a ≫ kanDiagramUnit K F' = kanDiagramUnit K F ≫ kanDiagramMap K a := by
    ext k n x
    exact congrArg (fun q => q.app n x)
      (AnodyneKanReplacement.unit.naturality (a.app k))
  rw [← Category.assoc, hn, Category.assoc, ← Functor.whiskerRight_comp, h,
    Functor.whiskerRight_comp, ← Category.assoc]

/-- 概要：共通図式を介する Kan 錐の比較同型は自然（Hovey §5.4）。
方針：右比較の後合成で判定し、元の二つの可換四角形を使う。
規約：二つの図式の三本の射と元の比較をそのまま保持する。
使われ方：始域・終域 frame の錐の比較を関手の比較へ束ねる。 -/
lemma kanConeComparisonIso_naturality {F G H F' G' H' : K ⥤ SSet.{u}}
    (f : F ⟶ H) (g : G ⟶ H) (f' : F' ⟶ H') (g' : G' ⟶ H')
    (hF : ∀ k, SSet.KanComplex (F.obj k)) (hG : ∀ k, SSet.KanComplex (G.obj k))
    (hF' : ∀ k, SSet.KanComplex (F'.obj k)) (hG' : ∀ k, SSet.KanComplex (G'.obj k))
    (hf : ∀ k, IsIso (AnodyneHomotopy.anodyneQ.map (f.app k)))
    (hg : ∀ k, IsIso (AnodyneHomotopy.anodyneQ.map (g.app k)))
    (hf' : ∀ k, IsIso (AnodyneHomotopy.anodyneQ.map (f'.app k)))
    (hg' : ∀ k, IsIso (AnodyneHomotopy.anodyneQ.map (g'.app k)))
    (a : F ⟶ F') (b : G ⟶ G') (c : H ⟶ H')
    (hleft : a ≫ f' = f ≫ c) (hright : b ≫ g' = g ≫ c) :
    L.map ((coneSpace K W).map a) ≫
        (kanConeComparisonIso K W hW L hL f' g' hF' hG' hf' hg').hom =
      (kanConeComparisonIso K W hW L hL f g hF hG hf hg).hom ≫
        L.map ((coneSpace K W).map b) := by
  have := coneComparisonArrow_isIso K W hW L hL g' hG' hg'
  apply (cancel_mono (coneComparisonArrow K W L g')).mp
  rw [Category.assoc, kanConeComparisonIso_fac, Category.assoc,
    coneComparisonArrow_naturality K W L g g' b c hright, ← Category.assoc,
    kanConeComparisonIso_fac, coneComparisonArrow_naturality K W L f f' a c hleft]

end SerrePositivity.EInfinity.HomotopyWeight
