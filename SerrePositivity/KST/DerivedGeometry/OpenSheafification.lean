module

public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.CategoryTheory.Sites.CoverLifting

/-!
# 開部分への制限と層化

概要：開埋め込みに沿う制限は層化と可換。
方針：開像の関手の連続性と余連続性を使う。
規約：値の圏と必要な層化・右 Kan 拡張の存在を明示する。
使われ方：KST D4、Toën Derived Azumaya §3.2 の係数環層の局所比較。
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory TopologicalSpace

namespace SerrePositivity.KST.DerivedGeometry

variable {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : Topology.IsOpenEmbedding f)

/--
概要：開埋め込みの開像の関手は連続。
方針：Mathlib の開埋め込みの被覆保存の定理を使う。
規約：開集合の通常のサイトを扱う。
使われ方：KST D4、Toën §3.2 の係数環層の制限。
-/
instance openEmbedding_isContinuous :
    hf.functor.IsContinuous (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology Y) := hf.functor_isContinuous

/--
概要：開埋め込みの開像の関手は余連続。
方針：開像と逆像の随伴を使い、逆像の被覆保存へ帰着する。
規約：始域と終域の開集合の通常の Grothendieck 位相を使う。
使われ方：KST D4、Toën §3.2 の制限と層化の可換性。
-/
instance openEmbedding_isCocontinuous :
    hf.functor.IsCocontinuous (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology Y) :=
  (hf.isOpenMap.adjunction.isCocontinuous_iff_coverPreserving _ _).mpr
    (coverPreserving_opens_map f)

variable (C : Type v) [Category.{w} C]
  [HasWeakSheafify (Opens.grothendieckTopology X) C]
  [HasWeakSheafify (Opens.grothendieckTopology Y) C]
  [∀ (P : (Opens X)ᵒᵖ ⥤ C), hf.functor.op.HasPointwiseRightKanExtension P]

/--
概要：開埋め込みの制限と層化の標準的な自然同型。
方針：連続かつ余連続なサイトの関手についての層化の比較を使う。
規約：前層の制限は開像の関手による前合成とする。
使われ方：KST D4、Toën §3.2 の係数前層から層への局所比較。
-/
def openSheafificationIso (P : Y.Presheaf C) :
    (presheafToSheaf (Opens.grothendieckTopology X) C).obj (hf.functor.op ⋙ P) ≅
      (hf.functor.sheafPushforwardContinuous C (Opens.grothendieckTopology X)
        (Opens.grothendieckTopology Y)).obj
          ((presheafToSheaf (Opens.grothendieckTopology Y) C).obj P) := by
  letI := hf.functor_isContinuous
  letI := openEmbedding_isCocontinuous hf
  exact (hf.functor.pushforwardContinuousSheafificationCompatibility C
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).app P

/--
概要：開部分への層化比較は層化の単位と可換。
方針：サイトの層化比較の指定された単位との計算式を使う。
規約：制限した前層から制限した層化への射を同定する。
使われ方：KST D4、Toën §3.2 の係数環層の構造射との両立。
-/
lemma openSheafificationIso_fac (P : Y.Presheaf C) :
    toSheafify (Opens.grothendieckTopology X) (hf.functor.op ⋙ P) ≫
      (openSheafificationIso hf C P).hom.hom =
    Functor.whiskerLeft hf.functor.op (toSheafify (Opens.grothendieckTopology Y) P) := by
  exact hf.functor.toSheafify_pullbackSheafificationCompatibility C
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) P

end SerrePositivity.KST.DerivedGeometry
