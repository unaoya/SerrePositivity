module

public import SerrePositivity.KST.DerivedGeometry.CoefficientSheaf
public import Mathlib.Topology.Sheaves.Module

/-!
# 開部分の加群とスライスサイトの準連接性

概要：開部分への構造層加群の制限を、開集合のスライスサイトへの制限と比較する。
方針：Mathlib の二つの層サイトの同値と恒等切断上の比較を使う。
規約：導来圏の降下はこの局所判定に含まれない。
使われ方：KST D4・T1、Toën Derived Azumaya §3.2 の準連接性の局所判定。
-/

@[expose] public section

noncomputable section

set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry
open TopologicalSpace

namespace SerrePositivity.KST.DerivedGeometry

variable {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)

/--
概要：開部分への加群の制限が準連接ならスライスサイトへの制限も準連接。
方針：既存の overFunctorEquiv とサイト同値の逆による準連接性保存を使う。
規約：二つの制限模型を Mathlib の標準同値で比較する。
使われ方：KST D4、Toën §3.2 の開被覆による準連接性判定。
-/
theorem moduleOver_isQuasicoherent_of_restrict
    [((Scheme.Modules.restrictFunctor U.ι).obj M).IsQuasicoherent] :
    (M.over U).IsQuasicoherent := by
  let : U.overEquivalence.functor.IsDenseSubsite
      ((Opens.grothendieckTopology X).over U)
      (Opens.grothendieckTopology (↥(U : Set X))) :=
    Opens.instIsDenseSubsiteOverSubtypeMemOverGrothendieckTopologyFunctorOverEquivalence
      (X := (X : TopCat)) U
  let e := Scheme.Modules.overEquiv U
  have : (e.functor.obj (M.over U)).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).prop_of_iso
      ((Scheme.Modules.overFunctorEquiv U).app M).symm inferInstance
  have (V : Over U) :
      (Over.post U.overEquivalence.functor).IsContinuous
        (((Opens.grothendieckTopology X).over U).over V)
        ((Opens.grothendieckTopology (↥(U : Set X))).over (U.overEquivalence.functor.obj V)) := by
    exact Functor.isContinuous_of_coverPreserving
      (compatiblePreservingOfFlat _ (Over.post U.overEquivalence.functor))
      ((Functor.IsDenseSubsite.coverPreserving
        ((Opens.grothendieckTopology X).over U)
        (Opens.grothendieckTopology (↥(U : Set X))) U.overEquivalence.functor).overPost V)
  have h : (e.inverse.obj (e.functor.obj (M.over U))).IsQuasicoherent :=
    SheafOfModules.isQuasicoherent_pushforward_of_isLeftAdjoint
      U.overEquivalence.functor (U.sheafRestrictSheafEquivOver.app X.ringCatSheaf).inv
      (U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf)
  exact (SheafOfModules.isQuasicoherent (X.ringCatSheaf.over U)).prop_of_iso
    (e.unitIso.app (M.over U)).symm h

/--
概要：構造層加群の準連接性は開被覆上で判定できる。
方針：開部分の制限をスライスサイトへ移し、準連接データの被覆上の貼り合わせを使う。
規約：被覆は開集合の上限が全体となる条件で指定する。
使われ方：KST D4・T1、Toën §3.2 のアフィン被覆への局所化。
-/
theorem module_isQuasicoherent_of_openCover {I : Type u} (V : I → X.Opens)
    (hV : iSup V = ⊤)
    [∀ i, ((Scheme.Modules.restrictFunctor (V i).ι).obj M).IsQuasicoherent] :
    M.IsQuasicoherent := by
  have (i : I) : (M.over (V i)).IsQuasicoherent :=
    moduleOver_isQuasicoherent_of_restrict M (V i)
  exact SheafOfModules.IsQuasicoherent.of_coversTop M V ((Opens.coversTop_iff X V).mpr hV)

end SerrePositivity.KST.DerivedGeometry
