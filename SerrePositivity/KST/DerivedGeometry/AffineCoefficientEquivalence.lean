module

public import SerrePositivity.KST.DerivedGeometry.AffineTildeCoefficientAction
public import SerrePositivity.KST.DerivedGeometry.CoefficientActionSheaf

/-!
概要：アフィン上の準連接係数加群層と H 加群の圏同値を構成する。
方針：通常の tilde 層を保持して H 作用を層化し、大域切断の単位を H 線形同型にする。
規約：H の平坦性・可換性を仮定しない。導来同値は別の工程。
使われ方：KST D4・T1′、Toën §3.2 のアフィン係数加群圏。
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
概要：左 H 加群からアフィン係数加群層を構成する。
方針：基礎 R 加群の tilde 層に移した H 作用を係数環層の作用へ拡張する。
規約：基礎 O 加群は通常の tilde 層と同型。
使われ方：KST D4・T1′、Toën §3.2 のアフィン比較の逆向きの対象構成。
-/
def affineCoefficientTilde (M : ModuleCat.{u} H) :
    (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).QCoh := by
  let V := (ModuleCat.restrictScalars (algebraMap R H)).obj M
  let ρ := affineTildeActionRingHom (R := R) H M
  let hρ := affineTildeAction_base (R := R) H M
  let N := coefficientModuleOfAction H (Scheme.ΓSpecIso R).inv.hom (tilde V) ρ hρ
  refine ⟨N, ?_⟩
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
    (coefficientModuleOfActionForgetIso H (Scheme.ΓSpecIso R).inv.hom (tilde V) ρ hρ).symm
      (show (tilde V).IsQuasicoherent from inferInstance)

/--
概要：H 加群から構成した係数 tilde 層の大域切断は元の H 加群と同型。
方針：通常の tilde の単位同型と H の各作用射の自然性から H 線形性を示す。
規約：基礎加法群の同型は通常の tilde の単位を保持する。
使われ方：KST D4・T1′、Toën §3.2 の本質的全射性。
-/
def affineCoefficientTildeUnit (M : ModuleCat.{u} H) :
    M ≅ (affineQcohΓ (R := R) H).obj (affineCoefficientTilde (R := R) H M) := by
  let V := (ModuleCat.restrictScalars (algebraMap R H)).obj M
  let ρ := affineTildeActionRingHom (R := R) H M
  let hρ := affineTildeAction_base (R := R) H M
  let e := (tilde.toTildeΓNatIso (R := R)).app V
  refine ModuleCat.isoMk ((forget₂ (ModuleCat R) AddCommGrpCat).mapIso e) ?_
  intro h
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro m
  change M at m
  change (tensorCoefficientConstant H (Scheme.ΓSpecIso R).inv.hom).app (.op ⊤) h •
      (show (affineCoefficientTilde (R := R) H M).obj.val.obj (.op ⊤) from e.hom.hom m) =
    (show (affineCoefficientTilde (R := R) H M).obj.val.obj (.op ⊤) from e.hom.hom (h • m))
  have hc := coefficientModuleOfAction_constant_smul H (Scheme.ΓSpecIso R).inv.hom
    (tilde V) ρ hρ ⊤ h (e.hom.hom m)
  have hn := congrArg (fun f : V ⟶ moduleSpecΓFunctor.obj (tilde V) => f.hom m)
    (affineTildeAction_unit (R := R) H M h)
  change e.hom.hom (h • m) = ((ρ h).asHom.val.app (.op ⊤)).hom (e.hom.hom m) at hn
  exact hc.trans hn.symm

/--
概要：アフィン上の準連接係数加群層の大域切断関手は本質的全射。
方針：任意の H 加群に対する係数 tilde 層と、その H 線形単位同型を使う。
規約：存在を未証明の仮定として入力しない。
使われ方：KST D4・T1′、Toën §3.2 のアフィン係数同値。
-/
instance affineQcohΓ_essSurj : (affineQcohΓ (R := R) H).EssSurj where
  mem_essImage M := ⟨affineCoefficientTilde (R := R) H M,
    ⟨(affineCoefficientTildeUnit (R := R) H M).symm⟩⟩

/--
概要：アフィン準連接係数加群層の大域切断関手は圏同値。
方針：完全忠実性と実際の係数 tilde 層による本質的全射性を束ねる。
規約：H の非可換性を許す。
使われ方：KST D4・T1′、Toën §3.2 のアフィン導来比較の層レベルの入力。
-/
instance affineQcohΓ_isEquivalence : (affineQcohΓ (R := R) H).IsEquivalence where

/--
概要：アフィン上の準連接 H_X 加群層と左 H 加群の圏同値。
方針：同じ大域切断関手を証明済みの同値性と束ねる。
規約：Dqc の定義は層導来圏内の準連接コホモロジーの条件として保持する。
使われ方：KST D4・T1′、Toën §3.2 のアフィン係数加群圏。
-/
def affineCoefficientEquivalence :
    (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).QCoh ≌ ModuleCat.{u} H :=
  (affineQcohΓ (R := R) H).asEquivalence

end SerrePositivity.KST.DerivedGeometry
