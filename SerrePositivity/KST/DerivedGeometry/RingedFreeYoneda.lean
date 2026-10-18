module

public import SerrePositivity.KST.DerivedGeometry.FreePresheafCech
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

/-!
概要：任意の環層上の開の切断を表す自由 Yoneda 加群層。
方針：前層の自由加群関手と Yoneda、実際の加群層化を合成する。
規約：環層の可換性・平坦性を要求しない。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の係数 Čech とアフィン導来比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits TopologicalSpace
namespace SerrePositivity.KST.DerivedGeometry
variable (X : TopCat.{u}) (B : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

/--
概要：開に対応する環前層上の自由 Yoneda 加群前層の関手。
方針：Mathlib の Yoneda と前層の自由加群関手を合成する。
規約：各開 W では B(W) 上の Hom(W,U) の自由加群。
使われ方：TT §3、Toën §3.2 の係数自由 Čech の局所計算。
-/
def ringedFreePresheafOnOpen : Opens X ⥤ PresheafOfModules.{u} B.obj :=
  yoneda ⋙ PresheafOfModules.free B.obj

/--
概要：開の切断を表す環層上の実際の自由加群層の関手。
方針：自由 Yoneda 加群前層を元の環層上で層化する。
規約：元の係数環層の加群圏内の対象。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の係数 Ext の始域。
-/
def ringedFreeSheafOnOpen : Opens X ⥤ SheafOfModules.{u} B :=
  ringedFreePresheafOnOpen X B ⋙ PresheafOfModules.sheafification (𝟙 B.obj)

/--
概要：環層上の自由層からの射は同じ開の実際の切断と同値。
方針：加群層化の随伴と前層の自由 Yoneda の同値を合成する。
規約：存在や比較を未証明の構造体フィールドとして要求しない。
使われ方：TT §3、BvdB Thm 3.1.1、Toën §3.2 の係数 Ext の cocycle。
-/
def ringedFreeSheafOnOpenHomEquiv (U : Opens X) (F : SheafOfModules.{u} B) :
    ((ringedFreeSheafOnOpen X B).obj U ⟶ F) ≃ F.val.obj (.op U) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 B.obj)).homEquiv _ F).trans
    PresheafOfModules.freeYonedaEquiv

/--
概要：自由 Yoneda 加群前層の W 上の評価は B(W) 上の表現可能自由加群と自然同型。
方針：元と射の両方を元の Yoneda の写像で比較する。
規約：評価する開 W ごとに係数環は実際の B(W)。
使われ方：TT §3、Toën §3.2 の局所収縮の係数版。
-/
def ringedFreePresheafEvaluationIso (W : Opens X) :
    ringedFreePresheafOnOpen X B ⋙ PresheafOfModules.evaluation B.obj (.op W) ≅
      coyoneda.obj (.op W) ⋙ ModuleCat.free (B.obj.obj (.op W)) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

/--
概要：形式的余積の自由加群前層を評価すると表現可能自由加群の余積と自然同型。
方針：前層評価の余積保存と自由 Yoneda の評価同型を合成する。
規約：全ての形式的余積の射と両立する。
使われ方：TT §3・§8、Toën §3.2 の環層係数の Čech の評価比較。
-/
def ringedFreeFormalPresheafEvaluationIso (W : Opens X) :
    (FormalCoproduct.eval (Opens X) (PresheafOfModules.{u} B.obj)).obj
        (ringedFreePresheafOnOpen X B) ⋙ PresheafOfModules.evaluation B.obj (.op W) ≅
      formalCoproductMapFunctor (coyoneda.obj (.op W)) ⋙
        (FormalCoproduct.eval (Type u) (ModuleCat.{u} (B.obj.obj (.op W)))).obj
          (ModuleCat.free (B.obj.obj (.op W))) :=
  formalCoproductEvalCovariantIso (ringedFreePresheafOnOpen X B)
      (PresheafOfModules.evaluation B.obj (.op W)) ≪≫
    (FormalCoproduct.eval (Opens X) (ModuleCat.{u} (B.obj.obj (.op W)))).mapIso
      (ringedFreePresheafEvaluationIso X B W)

end SerrePositivity.KST.DerivedGeometry
