module

public import SerrePositivity.KST.DerivedGeometry.AffineCoefficientAbelian
public import SerrePositivity.KST.DerivedGeometry.AffineTildeExact

/-!
概要：係数 tilde の全加群層への関手と通常の tilde との自然比較。
方針：実際のアフィン係数同値と tilde の余単位を使う。
規約：H の可換性・平坦性は不要。
使われ方：Bondal–van den Bergh Thm 3.1.1、TT §3、Toën §3.2 のアフィン比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory AlgebraicGeometry
namespace SerrePositivity.KST.DerivedGeometry
variable {R : CommRingCat.{u}} (H : Type u) [Ring H] [Algebra R H]

/--
概要：準連接係数加群層の基礎 O 加群層は通常の tilde の余単位で復元される。
方針：準連接性による余単位の同型性を全対象で束ねる。
規約：元の基礎加群層の射を保持する。
使われ方：TT §3、Toën §3.2 の係数 tilde の完全性。
-/
def affineQcohUnderlyingCounit :
    ((tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).qcohInclusion ⋙
      (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).forget) ⋙
        moduleSpecΓFunctor ⋙ tilde.functor R ≅
    (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).qcohInclusion ⋙
      (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).forget := by
  let F := (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).qcohInclusion ⋙
    (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).forget
  let τ := Functor.whiskerLeft F (tilde.adjunction (R := R)).counit
  have (M : (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).QCoh) :
      IsIso (τ.app M) := by
    let : (F.obj M).IsQuasicoherent := M.property
    change IsIso (Scheme.Modules.fromTildeΓ (F.obj M))
    infer_instance
  have : IsIso τ := NatIso.isIso_of_isIso_app τ
  exact asIso τ

/--
概要：準連接係数加群層の忘却は大域切断の H 加群を R へ制限した tilde と自然同型。
方針：大域切断の忘却比較を tilde の余単位と合成する。
規約：対象ごとの存在だけでなく関手の自然同型を与える。
使われ方：Toën §3.2 の係数 tilde の完全性の移送。
-/
def affineQcohUnderlyingTildeIso :
    (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).qcohInclusion ⋙
      (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).forget ≅
    affineQcohΓ (R := R) H ⋙ ModuleCat.restrictScalars (algebraMap R H) ⋙ tilde.functor R := by
  let F := (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).qcohInclusion ⋙
    (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).forget
  let e : affineQcohΓ (R := R) H ⋙ ModuleCat.restrictScalars (algebraMap R H) ≅
      F ⋙ moduleSpecΓFunctor := affineQcohΓForgetIso H
  exact ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight e (tilde.functor R) ≪≫
    Functor.associator _ _ _ ≪≫ affineQcohUnderlyingCounit H).symm

/--
概要：左 H 加群を全係数加群層へ送るアフィン tilde 関手。
方針：証明済みのアフィン係数同値の逆関手と実際の充満部分圏の包含を合成する。
規約：標的は準連接複体の導来圏ではなく全加群層の圏。
使われ方：Bondal–van den Bergh Thm 3.1.1、Toën §3.2 の実際の Dqc への入口。
-/
def affineCoefficientTildeFunctor : ModuleCat.{u} H ⥤
    (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).Modules :=
  (affineCoefficientEquivalence (R := R) H).inverse ⋙
    (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).qcohInclusion

/--
概要：全加群層への係数 tilde を忘却すると通常の tilde と自然同型。
方針：準連接層の比較に係数同値の逆関手を前合成し、余単位で簡約する。
規約：基礎 R 加群への制限を明示する。
使われ方：TT §3、Toën §3.2 の係数 tilde の完全性。
-/
def affineCoefficientTildeForgetIso :
    affineCoefficientTildeFunctor (R := R) H ⋙
      (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).forget ≅
    ModuleCat.restrictScalars (algebraMap R H) ⋙ tilde.functor R :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (affineCoefficientEquivalence (R := R) H).inverse
      (affineQcohUnderlyingTildeIso H) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (affineCoefficientEquivalence (R := R) H).counitIso _ ≪≫
    Functor.leftUnitor _

end SerrePositivity.KST.DerivedGeometry
