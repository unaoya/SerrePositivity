module
public import SerrePositivity.HomologicalAlgebra.CopowerUnitHom
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions

/-!
概要：小さい添字の単位加群の指定余積を、持ち上げた添字の自由加群と同定する。
方針：両者からの射の生成元評価を使い、指定生成元を互いに送る。
規約：係数の宇宙は任意。添字の ULift を明記し、元の余積包含を保つ。
使われ方：HA 1.2.4、G10 の BK 線形重みと自由積 EZ 比較の接続。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
namespace SerrePositivity.HomologicalAlgebra
variable (A : Type u) [CommRing A]

/-- 指定余積から自由加群へ、標準生成元を送る射。 -/
def copowerUnitFreeHom (S : Type) :
    (copowerFunctor (ModuleCat.of A A)).obj S ⟶ (ModuleCat.free A).obj (ULift.{u} S) :=
  (copowerUnitHomEquiv A S _).symm (fun s => ModuleCat.freeMk (ULift.up s))

/-- 自由加群から指定余積へ、同じ生成元を戻す射。 -/
def copowerUnitFreeInv (S : Type) :
    (ModuleCat.free A).obj (ULift.{u} S) ⟶ (copowerFunctor (ModuleCat.of A A)).obj S :=
  ModuleCat.freeDesc (↾fun s => Sigma.ι (fun _ : S => ModuleCat.of A A) s.down (1 : A))

/-- 余積側の指定生成元の像。 -/
@[simp]
theorem copowerUnitFreeHom_generator (S : Type) (s : S) :
    copowerUnitFreeHom A S (Sigma.ι (fun _ : S => ModuleCat.of A A) s (1 : A)) =
      ModuleCat.freeMk (ULift.up s) :=
  congrFun ((copowerUnitHomEquiv A S _).apply_symm_apply _) s

/-- 自由側の指定生成元の像。 -/
@[simp]
theorem copowerUnitFreeInv_generator (S : Type) (s : ULift.{u} S) :
    copowerUnitFreeInv A S (ModuleCat.freeMk s) =
      Sigma.ι (fun _ : S => ModuleCat.of A A) s.down (1 : A) :=
  ModuleCat.freeDesc_apply _ _

/-- 指定生成元を保つ、余積と持ち上げた自由加群の同型。 -/
def copowerUnitFreeIso (S : Type) :
    (copowerFunctor (ModuleCat.of A A)).obj S ≅ (ModuleCat.free A).obj (ULift.{u} S) where
  hom := copowerUnitFreeHom A S
  inv := copowerUnitFreeInv A S
  hom_inv_id := by
    apply (copowerUnitHomEquiv A S _).injective
    funext s
    change copowerUnitFreeInv A S (copowerUnitFreeHom A S
      (Sigma.ι (fun _ : S => ModuleCat.of A A) s (1 : A))) = _
    erw [copowerUnitFreeHom_generator A S s, copowerUnitFreeInv_generator A S (ULift.up s)]
    rfl
  inv_hom_id := by
    apply ModuleCat.free_hom_ext
    intro s
    change copowerUnitFreeHom A S (copowerUnitFreeInv A S (ModuleCat.freeMk s)) = _
    erw [copowerUnitFreeInv_generator A S s, copowerUnitFreeHom_generator A S s.down]
    rfl

/-- 同じ同型は添字集合の全写像に自然。 -/
@[reassoc]
theorem copowerUnitFreeIso_naturality {S T : Type} (f : S ⟶ T) :
    (copowerFunctor (ModuleCat.of A A)).map f ≫ (copowerUnitFreeIso A T).hom =
      (copowerUnitFreeIso A S).hom ≫
        (ModuleCat.free A).map (uliftFunctor.{u,0}.map f) := by
  apply (copowerUnitHomEquiv A S _).injective
  rw [copowerUnitHomEquiv_precomp]
  funext s
  change copowerUnitFreeHom A T (Sigma.ι (fun _ : T => ModuleCat.of A A) (f s) (1 : A)) =
    (ModuleCat.free A).map (uliftFunctor.{u,0}.map f)
      (copowerUnitFreeHom A S (Sigma.ι (fun _ : S => ModuleCat.of A A) s (1 : A)))
  erw [copowerUnitFreeHom_generator A T (f s), copowerUnitFreeHom_generator A S s,
    ModuleCat.free_map_apply]
  rfl

/-- 全添字の自然同型。 -/
def copowerUnitFreeNatIso :
    copowerFunctor (ModuleCat.of A A) ≅ uliftFunctor.{u,0} ⋙ ModuleCat.free A :=
  NatIso.ofComponents (copowerUnitFreeIso A) (fun f => copowerUnitFreeIso_naturality A f)

end SerrePositivity.HomologicalAlgebra
