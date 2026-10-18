module

public import SerrePositivity.KST.Comparison.SliceAdjunction
public import Mathlib.CategoryTheory.Limits.Over

/-!
# 余錐の基底上への持ち上げと引き戻し

概要：余錐の頂点から基底への射を指定すると、その余錐をスライス圏へ持ち上げられる。
方針：各構造写像と基底射を合成し、forget の余極限の反映を使う。
規約：Segal 1974 Proposition 1.6 の境界の被覆に沿うファイバー比較の補助。
使われ方：固定した射の厳密ファイバーと余極限の交換。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits
variable {D : Type v} [Category.{w} D] {Y : D ⥤ SSet.{u}} {B : SSet.{u}}

/--
概要：余錐の図式を頂点からの射により基底上の図式にする。
方針：各構造写像に基底への射を合成する。
規約：図式の添字の圏は任意。
使われ方：スライスの引き戻し関手を図式全体へ適用する。
-/
def coconeOverDiagram (c : Cocone Y) (g : c.pt ⟶ B) : D ⥤ Over B where
  obj d := Over.mk (c.ι.app d ≫ g)
  map {d e} θ := Over.homMk (Y.map θ) (by
    change Y.map θ ≫ (c.ι.app e ≫ g) = c.ι.app d ≫ g
    rw [← Category.assoc, c.w θ])
  map_id d := Over.OverMorphism.ext (Y.map_id d)
  map_comp θ φ := Over.OverMorphism.ext (Y.map_comp θ φ)

/--
概要：基底上へ持ち上げた図式の標準余錐。
方針：元の構造写像をスライス圏の射と読む。
規約：頂点は指定した基底射そのもの。
使われ方：引き戻しの余錐を取る前の構造。
-/
def coconeOverCocone (c : Cocone Y) (g : c.pt ⟶ B) : Cocone (coconeOverDiagram c g) where
  pt := Over.mk g
  ι :=
    { app d := Over.homMk (c.ι.app d)
      naturality {d e} θ := Over.OverMorphism.ext (by
        change Y.map θ ≫ c.ι.app e = c.ι.app d
        exact c.w θ) }

/--
概要：元の余錐が余極限なら、基底上に持ち上げた余錐も余極限である。
方針：スライスからの forget が余極限を反映することを使う。
規約：基底への射の普遍性は新しく仮定しない。
使われ方：固定したファイバー関手の余極限保存。
-/
def coconeOverCoconeIsColimit (c : Cocone Y) (hc : IsColimit c) (g : c.pt ⟶ B) :
    IsColimit (coconeOverCocone c g) := by
  apply isColimitOfReflects (Over.forget B)
  exact hc

/--
概要：固定射の厳密ファイバーを各項に取った余錐。
方針：スライスのファイバー関手を持ち上げた余錐へ適用する。
規約：頂点は元の余錐の頂点と指定した射の引き戻し。
使われ方：比較射の被覆に沿う貼り合わせ。
-/
def fiberCocone {E : SSet.{u}} (p : E ⟶ B) (c : Cocone Y) (g : c.pt ⟶ B) :
    Cocone (coconeOverDiagram c g ⋙ sliceFiberFunctor p) :=
  (sliceFiberFunctor p).mapCocone (coconeOverCocone c g)

/--
概要：固定射の厳密ファイバーを取っても、指定した余錐の余極限性は保たれる。
方針：ファイバー関手が左随伴であることによる余極限保存を使う。
規約：指定した射の Kan 性は不要。
使われ方：ホモトピー引き戻しへの比較の余積・pushout の貼り合わせ。
-/
def fiberCoconeIsColimit {E : SSet.{u}} (p : E ⟶ B)
    (c : Cocone Y) (hc : IsColimit c) (g : c.pt ⟶ B) : IsColimit (fiberCocone p c g) :=
  isColimitOfPreserves (sliceFiberFunctor p) (coconeOverCoconeIsColimit c hc g)

/--
概要：ファイバーの余錐の構造写像の第一射影。
方針：スライスのファイバー関手の射の第一射影を計算する。
規約：第一成分では元の余錐の構造写像を合成する。
使われ方：標準比較射の余錐との可換性。
-/
@[reassoc] theorem fiberCocone_ι_fst {E : SSet.{u}} (p : E ⟶ B)
    (c : Cocone Y) (g : c.pt ⟶ B) (d : D) :
    (fiberCocone p c g).ι.app d ≫ pullback.fst g p =
      pullback.fst (c.ι.app d ≫ g) p ≫ c.ι.app d :=
  sliceFiberFunctor_map_fst p
    (Over.homMk (U := Over.mk (c.ι.app d ≫ g)) (V := Over.mk g) (c.ι.app d) rfl)

/--
概要：ファイバーの余錐の構造写像の第二射影。
方針：固定した全空間の成分は変わらないことを使う。
規約：第二成分は固定した射の始域へ入る。
使われ方：標準比較射の余錐との可換性。
-/
@[reassoc] theorem fiberCocone_ι_snd {E : SSet.{u}} (p : E ⟶ B)
    (c : Cocone Y) (g : c.pt ⟶ B) (d : D) :
    (fiberCocone p c g).ι.app d ≫ pullback.snd g p = pullback.snd (c.ι.app d ≫ g) p :=
  sliceFiberFunctor_map_snd p
    (Over.homMk (U := Over.mk (c.ι.app d ≫ g)) (V := Over.mk g) (c.ι.app d) rfl)

end SerrePositivity.KST.Comparison
