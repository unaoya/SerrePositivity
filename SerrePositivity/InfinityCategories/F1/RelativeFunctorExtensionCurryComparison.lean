module

public import SerrePositivity.InfinityCategories.F1.RelativeFunctorExtensionEndpoint
public import SerrePositivity.InfinityCategories.F1.RelativeFunctorCurryHom

/-!
概要：相対延長の終点の比較をパラメーター付き相対関手の間の関手同型へ移す。
方針：可縮な延長空間の終点の頂点同型を相対 curry の豊穣作用で写す。
規約：終点の定義域は C とパラメーター L の直積で、底の図式は L に関して定値。
使われ方：Kerodon Corollary 5.6.0.6、写像空間上の unstraightening の自然性の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：共通の初期値を持つ二つの相対延長の終点の族は、相対 curry の後で関手同型。
方針：延長の終点の頂点同型と相対 curry による関手同型の構成を合成する。
規約：i は left anodyne、j は C⊗L からの任意の評価射。
使われ方：Kerodon Corollary 5.6.0.6、底変換の二通りの写像族の比較。 -/
noncomputable def relativeFunctorExtensionEndpoint_curryIso
    {A D C E F B L : SSet.{u}} (p : E ⟶ B) [LeftFibration p]
    (b : A ⟶ B) (i : D ⟶ A) (hi : leftAnodyneExtensions i)
    (v : D ⟶ E) (hv : v ≫ p = i ≫ b)
    (j : C ⊗ L ⟶ A) (q : F ⟶ B) (a : C ⟶ F)
    (hj : j ≫ b = (fst C L ≫ a) ≫ q)
    (W W' : A ⟶ E) (hW : W ≫ p = b) (hW' : W' ≫ p = b)
    (hWi : i ≫ W = v) (hWi' : i ≫ W' = v)
    (g g' : C ⊗ L ⟶ pullback p q)
    (hg : g ≫ pullback.snd p q = fst C L ≫ a)
    (hg' : g' ≫ pullback.snd p q = fst C L ≫ a)
    (hWj : j ≫ W = g ≫ pullback.fst p q)
    (hWj' : j ≫ W' = g' ≫ pullback.fst p q) :
    FunctorIso (relativeFunctorCurry g hg) (relativeFunctorCurry g' hg') :=
  relativeFunctorCurryIso (pullback.snd p q) a g g' hg hg'
    (relativeFunctorExtensionEndpoint_witnessIso p b i hi v hv j q (fst C L ≫ a) hj
      W W' hW hW' hWi hWi' g g' hg hg' hWj hWj')

end SerrePositivity.InfinityCategories
