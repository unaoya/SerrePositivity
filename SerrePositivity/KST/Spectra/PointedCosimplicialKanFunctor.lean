module

public import SerrePositivity.KST.Spectra.PointedCosimplicialKanReplacement

/-!
概要：点つき余単体 Reedy Kan 置換の関手性と単位の自然性。
方針：忘却した置換の自然変換を各値で基点を保存する射へ持ち上げる。
規約：関手法則と単位の自然性は厳密な等式。
使われ方：Goerss–Jardine I §7、HTT A.3.3。Tot の係数の自然な置換。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.PointedCosimplicialKanReplacement

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：余単体の点つき射を Reedy 置換の間の点つき射へ送る。
方針：置換の単位の自然性と元の基点保存の等式を使う。
規約：基礎射は忘却した Reedy 置換の射そのもの。
使われ方：Goerss–Jardine I §7。置換した Tot 係数への射。 -/
def map {X Y : CosimplicialObject PointedSimplicialSet.{u}} (f : X ⟶ Y) :
    obj X ⟶ obj Y where
  app j := Under.homMk
    ((CosimplicialKanReplacement.functor.map
      (Functor.whiskerRight f PointedSimplicialSet.forget)).app j) (by
      change ((X.obj j).hom ≫ _) ≫ _ = (Y.obj j).hom ≫ _
      have h := congr_app (CosimplicialKanReplacement.unit.naturality
        (Functor.whiskerRight f PointedSimplicialSet.forget)) j
      change (f.app j).right ≫ _ = _ ≫ _ at h
      rw [Category.assoc, ← h, ← Category.assoc, Under.w])
  naturality i j g := by
    apply Under.UnderMorphism.ext
    exact (CosimplicialKanReplacement.functor.map
      (Functor.whiskerRight f PointedSimplicialSet.forget)).naturality g

/-- 概要：点つき Reedy 置換は恒等射を保つ。
方針：基礎関手の恒等法則を各値へ移す。
規約：厳密な余単体射の等式。
使われ方：HTT A.3.3。置換の関手法則。 -/
lemma map_id (X : CosimplicialObject PointedSimplicialSet.{u}) :
    map (𝟙 X) = 𝟙 (obj X) := by
  apply NatTrans.ext
  funext j
  apply Under.UnderMorphism.ext
  exact congr_app (CosimplicialKanReplacement.functor.map_id
    (X ⋙ PointedSimplicialSet.forget)) j

/-- 概要：点つき Reedy 置換は射の合成を保つ。
方針：忘却した置換の合成法則を各値で使う。
規約：合成は厳密。
使われ方：HTT A.3.3。置換の関手法則。 -/
lemma map_comp {X Y Z : CosimplicialObject PointedSimplicialSet.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) : map (f ≫ g) = map f ≫ map g := by
  apply NatTrans.ext
  funext j
  apply Under.UnderMorphism.ext
  exact congr_app (CosimplicialKanReplacement.functor.map_comp
    (Functor.whiskerRight f PointedSimplicialSet.forget)
    (Functor.whiskerRight g PointedSimplicialSet.forget)) j

/-- 概要：点つき余単体 Reedy Kan 置換の実際の関手。
方針：対象・射と厳密な関手法則を束ねる。
規約：∞ 圏の極限関手という主張を含まない。
使われ方：Goerss–Jardine I §7。Tot に先立つ係数の置換。 -/
def functor : CosimplicialObject PointedSimplicialSet.{u} ⥤
    CosimplicialObject PointedSimplicialSet.{u} where
  obj := obj
  map := map
  map_id := map_id
  map_comp := map_comp

/-- 概要：点つき余単体図式からの単位は自然変換。
方針：基礎の Reedy 置換の単位の自然性を各値へ移す。
規約：単位は元の各値の Kan 性を仮定しない。
使われ方：Goerss–Jardine I §7、HTT A.3.3。Tot の標準比較の自然性。 -/
def unit : 𝟭 (CosimplicialObject PointedSimplicialSet.{u}) ⟶ functor where
  app := unitApp
  naturality X Y f := by
    apply NatTrans.ext
    funext j
    apply Under.UnderMorphism.ext
    exact congr_app (CosimplicialKanReplacement.unit.naturality
      (Functor.whiskerRight f PointedSimplicialSet.forget)) j

end

end SerrePositivity.KST.Spectra.PointedCosimplicialKanReplacement
