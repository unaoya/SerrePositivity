module

public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.Algebra.Homology.Additive

/-!
概要：交代面鎖複体への反変加法的関手と交代余面複体の比較。
方針：対圏と有限和・整数倍の保存を使って微分を比較する。
規約：同じ符号と全ての次数を保持する。
使われ方：TT §3・§8、Toën §3.2 の自由 Čech の Hom と通常の Čech の接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v a b
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {A : Type u} [Category.{v} A] [Preadditive A]
  {B : Type a} [Category.{b} B] [Preadditive B]

attribute [local simp] Functor.map_zsmul in
/--
概要：交代面鎖複体へ反変加法的関手を適用すると像の交代余面複体と同型。
方針：各項の恒等同型と対圏での微分の交代和の比較を使う。
規約：関手の完全性は同型の構成に不要。
使われ方：TT §3・§8、Toën §3.2 の Hom 余鎖複体。
-/
def alternatingFaceContravariantIso (F : Aᵒᵖ ⥤ B) [F.Additive] (X : SimplicialObject A) :
    (F.mapHomologicalComplex (.up ℕ)).obj
        (AlgebraicTopology.AlternatingFaceMapComplex.obj X).op ≅
      AlgebraicTopology.AlternatingCofaceMapComplex.obj (X.rightOp ⋙ F) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intro i j hij
    have hj : i + 1 = j := hij
    subst j
    simp [AlgebraicTopology.AlternatingFaceMapComplex.obj,
      AlgebraicTopology.AlternatingFaceMapComplex.objD,
      AlgebraicTopology.AlternatingCofaceMapComplex.obj,
      AlgebraicTopology.AlternatingCofaceMapComplex.objD,
      HomologicalComplex.op, Functor.map_sum, op_sum, op_zsmul,
      CosimplicialObject.δ, SimplicialObject.δ])

end SerrePositivity.KST.DerivedGeometry
