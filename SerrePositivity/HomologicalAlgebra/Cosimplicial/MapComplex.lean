module

public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Homology.Additive
import all Mathlib.AlgebraicTopology.AlternatingFaceMapComplex

/-!
# 加法的関手と交代余面複体

## 概要
各項に加法的関手を適用する操作は、交代余面複体を取る操作と可換。

## 方針
各次数を恒等同型で合わせ、微分の有限和を関手が保つことを使う。

## 規約
加法的関手についての古典的な複体の比較。完全性は仮定しない。

## 使われ方
BS 著者版 Theorem 6.4、各項の完備係数拡大を交代余面複体に移す。
-/

public noncomputable section
open CategoryTheory AlgebraicTopology
universe u v w w'
namespace SerrePositivity.Cosimplicial
set_option backward.isDefEq.respectTransparency false
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {D : Type w} [Category.{w'} D] [Preadditive D]

/-- 各項に加法的関手を適用してから交代余面複体を取る標準の比較。 -/
def alternatingCofaceMapComplexCompMapHomologicalComplexIso
    (F : C ⥤ D) [F.Additive] :
    alternatingCofaceMapComplex C ⋙ F.mapHomologicalComplex _ ≅
      (CosimplicialObject.whiskering C D).obj F ⋙ alternatingCofaceMapComplex D :=
  NatIso.ofComponents
    (fun X => HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _)
      (fun i j hij => by
        have hj : i + 1 = j := hij
        subst j
        change 𝟙 _ ≫ (AlternatingCofaceMapComplex.obj (X ⋙ F)).d i (i + 1) =
          F.map ((AlternatingCofaceMapComplex.obj X).d i (i + 1)) ≫ 𝟙 _
        simp [AlternatingCofaceMapComplex.obj, AlternatingCofaceMapComplex.objD, CosimplicialObject.δ, Functor.map_zsmul]))

end SerrePositivity.Cosimplicial
