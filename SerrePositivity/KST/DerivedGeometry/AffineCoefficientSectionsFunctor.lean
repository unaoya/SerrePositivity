module

public import SerrePositivity.KST.DerivedGeometry.AffineCoefficientGlobalRing
public import SerrePositivity.KST.DerivedGeometry.QuasicoherentCoefficient

/-!
# アフィン係数加群層の大域切断関手

概要：Spec R 上の係数加群層の大域切断を H 加群として取り、R への忘却と比較する。
方針：評価関手と定数切断に沿うスカラー制限を合成する。
規約：環 H の作用は指定された定数切断から与える。
使われ方：KST D4・T1′、Toën Derived Azumaya §3.2 のアフィン加群圏の比較。
-/

@[expose] public section

noncomputable section

set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry

namespace SerrePositivity.KST.DerivedGeometry

variable {R : CommRingCat.{u}} (H : Type u) [Ring H] [Algebra R H]

/--
概要：アフィン係数加群層の大域切断を H 加群とする関手。
方針：大域切断で評価し、H の定数切断の環準同型へスカラー制限する。
規約：全係数加群層で定義し、準連接性は別に制限する。
使われ方：KST D4・T1′、Toën §3.2 のアフィン比較の右関手。
-/
def affineCoefficientΓ :
    (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).Modules ⥤ ModuleCat.{u} H :=
  SheafOfModules.evaluation _ (.op ⊤) ⋙
    ModuleCat.restrictScalars
      ((tensorCoefficientConstant H (Scheme.ΓSpecIso R).inv.hom).app (.op ⊤)).hom

/--
概要：係数大域切断を R へ忘れたものと O 加群の大域切断を各対象で同定する。
方針：恒等写像に基礎環上の作用の一致による R 線形性を添える。
規約：基礎加法群と切断の値は変更しない。
使われ方：KST D4、Toën §3.2 の通常のアフィン準連接同値への接続。
-/
def affineCoefficientΓForgetIsoAt
    (M : (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).Modules) :
    ((affineCoefficientΓ H) ⋙ ModuleCat.restrictScalars (algebraMap R H)).obj M ≅
      ((tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).forget ⋙
        moduleSpecΓFunctor).obj M := by
  refine ModuleCat.isoMk (Iso.refl _) ?_
  intro r
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  change M.val.obj (.op ⊤) at x
  symm
  change ((tensorCoefficientConstant H (Scheme.ΓSpecIso R).inv.hom).app (.op ⊤))
      (algebraMap R H r) • x =
    (((tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).structureMap.hom).app (.op ⊤))
      (sectionBaseMap (Scheme.ΓSpecIso R).inv.hom ⊤ r) • x
  exact congrArg (fun b : (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).ring.obj.obj
      (.op ⊤) => b • x)
    (congrArg (fun g : R →+* _ => g r)
      (tensorCoefficientConstant_comp_algebraMap H (Scheme.ΓSpecIso R).inv.hom ⊤))

/--
概要：係数大域切断と係数忘却の比較は自然同型。
方針：切断上の恒等同型を自然変換として束ねる。
規約：R へのスカラー制限を明示する。
使われ方：KST D4、Toën §3.2 の準連接対象での大域切断の比較。
-/
def affineCoefficientΓForgetIso :
    affineCoefficientΓ (R := R) H ⋙ ModuleCat.restrictScalars (algebraMap R H) ≅
      (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).forget ⋙ moduleSpecΓFunctor :=
  NatIso.ofComponents (fun M => affineCoefficientΓForgetIsoAt H M)
    (fun f => by ext x; rfl)

/--
概要：準連接係数加群層の H 加群としての大域切断関手。
方針：全係数加群層の大域切断を充満部分圏へ制限する。
規約：圏の同値はまだ主張しない。
使われ方：KST D4・T1′、Toën §3.2 の係数アフィン同値への入力。
-/
def affineQcohΓ :
    (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).QCoh ⥤ ModuleCat.{u} H :=
  (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).qcohInclusion ⋙ affineCoefficientΓ H

/--
概要：準連接係数加群層の大域切断は、R へ忘れると通常の tilde 同値の逆と一致する。
方針：全係数加群層での比較を充満部分圏への前合成で制限する。
規約：Mathlib の tildeEquiv との自然同型として述べる。
使われ方：KST D4・T1′、Toën §3.2 の忠実性と同型反映の証明。
-/
def affineQcohΓForgetIso :
    affineQcohΓ (R := R) H ⋙ ModuleCat.restrictScalars (algebraMap R H) ≅
      (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).qcohForget ⋙
        (tildeEquiv (R := R)).inverse :=
  Functor.isoWhiskerLeft (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).qcohInclusion
    (affineCoefficientΓForgetIso H)

end SerrePositivity.KST.DerivedGeometry
