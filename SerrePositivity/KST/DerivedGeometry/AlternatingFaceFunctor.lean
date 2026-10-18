module

public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Homology.Additive

/-!
概要：交代面鎖複体と加法的関手の適用の自然比較。
方針：有限和・整数倍の保存で微分との両立を証明する。
規約：全次数の符号を保持する。
使われ方：TT §3・§8、Toën §3.2 の自由 Čech 鎖複体の評価。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe a b a' b'
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {A : Type a} [Category.{b} A] [Preadditive A]
  {B : Type a'} [Category.{b'} B] [Preadditive B]
  (F : A ⥤ B) [F.Additive]

attribute [local simp] Functor.map_zsmul in
/--
概要：交代面複体と加法的関手の適用は自然に可換。
方針：各項の恒等同型と微分の有限和・整数倍の保存を使う。
規約：交代符号を含む同じ微分を保持する。
使われ方：TT §3、Toën §3.2 の 自由 Čech 鎖複体の評価。
-/
def alternatingFaceCompMapIso :
    AlgebraicTopology.alternatingFaceMapComplex A ⋙ F.mapHomologicalComplex (.down ℕ) ≅
      (SimplicialObject.whiskering A B).obj F ⋙
        AlgebraicTopology.alternatingFaceMapComplex B :=
  NatIso.ofComponents
    (fun X => HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
      intro i j hij
      have hi : j + 1 = i := hij
      subst i
      simp [AlgebraicTopology.alternatingFaceMapComplex,
        AlgebraicTopology.AlternatingFaceMapComplex.obj,
        AlgebraicTopology.AlternatingFaceMapComplex.objD, Functor.map_sum,
        SimplicialObject.δ]))
    (by
      intros X Y f
      ext n
      simp [AlgebraicTopology.alternatingFaceMapComplex,
        AlgebraicTopology.AlternatingFaceMapComplex.map])

end SerrePositivity.KST.DerivedGeometry
