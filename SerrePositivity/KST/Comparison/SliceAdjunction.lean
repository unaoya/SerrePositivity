module

public import Mathlib.CategoryTheory.Comma.Presheaf.Basic
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.LiftingProperties.Adjunction
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic

/-!
# 単体集合のスライス圏の積と右随伴

概要：スライス内の固定対象との積を取って忘れる関手の右随伴を構成する。
方針：スライスと前層圏の同値を使い、閉構造を移送する。
規約：Segal 1974 Proposition 1.6 の基底変換の補助。宇宙は ULiftHom で揃える。
使われ方：horn ごとの左持ち上げ性を一般の anodyne 射へ拡張する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

attribute [local instance] Over.cartesianMonoidalCategory Over.braidedCategory

/--
概要：任意の宇宙の単体集合のスライスは閉構造を持つ。
方針：単体圏の Hom の宇宙を上げ、スライスと前層圏の同値に沿って閉構造を移す。
規約：比較に使う積は Mathlib の pullback から得る標準の積。
使われ方：基底変換に対する写像空間の随伴。
-/
@[instance_reducible]
def simplicialSliceClosed (B : SSet.{u}) : MonoidalClosed (Over B) := by
  let e : SSet.{u} ≌ ((ULiftHom.{u} SimplexCategory)ᵒᵖ ⥤ Type u) :=
    Equivalence.congrLeft (ULiftHom.equiv : SimplexCategory ≌ ULiftHom.{u} SimplexCategory).op
  let e' := (Over.postEquiv (X := B) e).trans
    (overEquivPresheafCostructuredArrow (e.functor.obj B))
  exact cartesianClosedOfEquiv e'.symm

/--
概要：基底上で固定した全空間との積を取り、基底の構造射を忘れる。
方針：スライスの tensorRight と忘却関手を合成する。
規約：対象 X→B の像は厳密な引き戻し X×_B E。
使われ方：Kan fibration に沿う anodyne 射の比較。
-/
def sliceFiberFunctor {E B : SSet.{u}} (p : E ⟶ B) : Over B ⥤ SSet.{u} :=
  tensorRight (Over.mk p) ⋙ Over.forget B

/--
概要：基底変換後に忘れる関手は左随伴である。
方針：スライスの閉構造と、忘却関手の積による右随伴を合成する。
規約：モデル構造の仮定を使わない圏論的な随伴。
使われ方：左持ち上げ性の随伴による移送。
-/
instance sliceFiberFunctor_isLeftAdjoint {E B : SSet.{u}} (p : E ⟶ B) :
    (sliceFiberFunctor p).IsLeftAdjoint := by
  let := simplicialSliceClosed B
  dsimp only [sliceFiberFunctor]
  infer_instance

/--
概要：基底変換関手が射に誘導する写像の第一射影。
方針：スライスの積の射影の計算則を使う。
規約：射の向きは X×_B E→Y×_B E。
使われ方：horn の逆像の標準比較射との一致。
-/
@[reassoc] theorem sliceFiberFunctor_map_fst {E B : SSet.{u}} (p : E ⟶ B)
    {X Y : Over B} (f : X ⟶ Y) :
    (sliceFiberFunctor p).map f ≫ pullback.fst Y.hom p = pullback.fst X.hom p ≫ f.left :=
  Over.whiskerRight_left_fst (R := Over.mk p) f

/--
概要：基底変換関手が射に誘導する写像の第二射影。
方針：スライスの積で固定した因子の射影を計算する。
規約：E の座標は保たれる。
使われ方：基底上の可換性と比較。
-/
@[reassoc] theorem sliceFiberFunctor_map_snd {E B : SSet.{u}} (p : E ⟶ B)
    {X Y : Over B} (f : X ⟶ Y) :
    (sliceFiberFunctor p).map f ≫ pullback.snd Y.hom p = pullback.snd X.hom p :=
  Over.whiskerRight_left_snd (R := Over.mk p) f

/--
概要：スライスの射に誘導される積の四角形は引き戻しである。
方針：標準引き戻しの長方形から右の引き戻し四角形を取り除く。
規約：構造射 X→B と Y→B の合成の一致を使う。
使われ方：horn の逆像の局所化同型を随伴の左側へ移す。
-/
theorem sliceFiberFunctor_map_isPullback {E B : SSet.{u}} (p : E ⟶ B)
    {X Y : Over B} (f : X ⟶ Y) :
    IsPullback ((sliceFiberFunctor p).map f) (pullback.fst X.hom p)
      (pullback.fst Y.hom p) f.left := by
  have outer : IsPullback ((sliceFiberFunctor p).map f ≫ pullback.snd Y.hom p)
      (pullback.fst X.hom p) p (f.left ≫ Y.hom) := by
    rw [sliceFiberFunctor_map_snd, Over.w f]
    exact (IsPullback.of_hasPullback X.hom p).flip
  exact outer.of_right (sliceFiberFunctor_map_fst p f)
    (IsPullback.of_hasPullback Y.hom p).flip

end SerrePositivity.KST.Comparison
