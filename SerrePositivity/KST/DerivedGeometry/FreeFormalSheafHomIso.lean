module

public import SerrePositivity.KST.DerivedGeometry.FreeFormalSheafHom

/-!
概要：自由層の形式的余積の Hom と切断の積の加法群の自然同型。
方針：加法的な Hom 同値と圏論的な積の標準比較を合成する。
規約：各射影との両立を証明して全ての形式的余積の射の自然性を検証する。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の Čech と Hom の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits TopologicalSpace
namespace SerrePositivity.KST.DerivedGeometry
variable (R : Type u) [Ring R] (X : TopCat.{u})
  (I : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))

/--
概要：自由層からの Hom の加法群は各開上の切断の圏論的な積と同型。
方針：加法的な Yoneda の同値を積の標準同型と合成する。
規約：係数を忘れた加法群の積で比較する。
使われ方：TT §3・§8、Toën §3.2 の Čech の各項の Hom 比較。
-/
def freeFormalSheafHomIso (Z : FormalCoproduct.{u} (Opens X)) :
    (preadditiveYoneda.obj I).obj (.op ((freeFormalSheafFunctor R X).obj Z)) ≅
      ∏ᶜ (fun i : Z.I => (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj
        (I.obj.obj (.op (Z.obj i)))) :=
  (freeFormalSheafHomAddEquiv R X Z I).toAddCommGrpIso ≪≫
    (additiveProductIsoPi (fun i : Z.I =>
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj (I.obj.obj (.op (Z.obj i))))).symm

/--
概要：自由層の Hom 比較を射影すると各開上の Yoneda の評価になる。
方針：積の標準同型の逆の射影公式を使う。
規約：実際の加法群の射の等式。
使われ方：TT §3、Toën §3.2 の Čech 微分の自然性。
-/
@[reassoc]
lemma freeFormalSheafHomIso_hom_π (Z : FormalCoproduct.{u} (Opens X)) (i : Z.I) :
    (freeFormalSheafHomIso R X I Z).hom ≫ Pi.π _ i =
      AddCommGrpCat.ofHom ((Pi.evalAddMonoidHom (fun i : Z.I => I.obj.obj (.op (Z.obj i))) i).comp
        (freeFormalSheafHomAddEquiv R X Z I).toAddMonoidHom) := by
  dsimp only [freeFormalSheafHomIso, Iso.trans_hom, Iso.symm_hom]
  rw [Category.assoc, additiveProductIsoPi_inv_π]
  rfl

/--
概要：形式的余積の自由層の Hom は切断による反変評価と自然同型。
方針：各項の加法群の比較を使い、射影ごとに自由前層の Yoneda の自然性を確認する。
規約：Čech の面と退化を含む全ての射と両立する。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の Čech と Hom の比較。
-/
def freeFormalSheafHomNatIso :
    (freeFormalSheafFunctor R X).op ⋙ preadditiveYoneda.obj I ≅
      (FormalCoproduct.evalOp (Opens X) AddCommGrpCat.{u}).obj
        (I.obj ⋙ forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) :=
  NatIso.ofComponents (fun Z => freeFormalSheafHomIso R X I Z.unop) (by
    intro Z Z' f
    apply Pi.hom_ext
    intro i
    simp only [Category.assoc, freeFormalSheafHomIso_hom_π, FormalCoproduct.evalOp,
      Functor.comp_map, Functor.comp_obj, Pi.lift_comp_π, Pi.lift_comp_π_assoc,
      freeFormalSheafHomIso_hom_π_assoc]
    ext g
    exact freeFormalSheafHomAddEquiv_naturality R X f.unop I g i)

end SerrePositivity.KST.DerivedGeometry
