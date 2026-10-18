module

public import SerrePositivity.KST.DerivedGeometry.FreePresheafHom

/-!
概要：開上の自由層からの Hom の加法性と標的自然性。
方針：層化の加法的随伴と自由前層の Hom 表示を合成する。
規約：非可換環でも加法群として比較する。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の Ext cocycle の切断表示。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits TopologicalSpace
namespace SerrePositivity.KST.DerivedGeometry
variable (R : Type u) [Ring R] (X : TopCat.{u}) (U : Opens X)

/--
概要：開上の自由層からの射と切断は加法的に同値。
方針：層化の加法的随伴と自由前層の既証の加法的同値を合成する。
規約：既存の Hom と切断の同値と同じ写像。
使われ方：TT §3、Toën §3.2 の cocycle と境界の表示。
-/
def freeModuleSheafOnOpenHomAddEquiv
    (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) :
    ((freeModuleSheafOnOpen R X).obj U ⟶ F) ≃+ F.obj.obj (.op U) :=
  ((sheafificationAdjunction _ _).homAddEquiv _ F).trans
    (freeModulePresheafOnOpenHomAddEquiv R X U F.obj)

/--
概要：自由層の Hom と切断の同値は標的層の射について自然。
方針：層化の随伴の右自然性を自由前層の生成元で評価する。
規約：標的の射の実際の U 成分を使う。
使われ方：TT §3、BvdB Thm 3.1.1、Toën §3.2 の微分との両立。
-/
lemma freeModuleSheafOnOpenHomEquiv_postcomp
    {F G : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)}
    (f : (freeModuleSheafOnOpen R X).obj U ⟶ F) (g : F ⟶ G) :
    freeModuleSheafOnOpenHomEquiv R X U G (f ≫ g) =
      g.hom.app (.op U) (freeModuleSheafOnOpenHomEquiv R X U F f) := by
  let A := sheafificationAdjunction (Opens.grothendieckTopology X) (ModuleCat.{u} R)
  have h := A.homEquiv_naturality_right f g
  exact congrArg (freeModulePresheafOnOpenHomEquiv R X U G.obj) h

/--
概要：自由層の零射は零切断へ対応する。
方針：同じ写像を持つ加法的同値の零の保存を使う。
規約：元の Hom 同値の表記で述べる。
使われ方：TT §3、Toën §3.2 の Ext cocycle の零微分。
-/
lemma freeModuleSheafOnOpenHomEquiv_zero
    (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) :
    freeModuleSheafOnOpenHomEquiv R X U F 0 = 0 :=
  (freeModuleSheafOnOpenHomAddEquiv R X U F).map_zero

end SerrePositivity.KST.DerivedGeometry
