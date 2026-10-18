module

public import SerrePositivity.KST.DerivedGeometry.AffineQuasicoherentActions
public import SerrePositivity.KST.DerivedGeometry.CoefficientLinearity

/-!
概要：アフィン準連接係数加群層の大域切断関手の充満性を証明する。
方針：通常の tilde 同値で O 加群層の射を戻し、大域 H 線形性から係数線形性を再構成する。
規約：係数環の可換性・平坦性を仮定しない。
使われ方：KST D4・T1′、Toën §3.2 のアフィン係数加群圏の比較。
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
概要：係数大域切断の射を基礎 O 加群層の射へ持ち上げる。
方針：R への忘却後の自然同型と通常の tilde 同値の充満性を使う。
規約：得られる射の大域切断の値は元の H 線形写像そのもの。
使われ方：KST D4・T1′、Toën §3.2 の係数作用の再構成。
-/
theorem affineUnderlyingHom_lift
    (M N : (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).QCoh)
    (g : (affineQcohΓ H).obj M ⟶ (affineQcohΓ H).obj N) :
    ∃ φ : (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).forget.obj M.obj ⟶
        (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).forget.obj N.obj,
      ∀ m : M.obj.val.obj (.op ⊤), (φ.val.app (.op ⊤)).hom m = g.hom m := by
  let B := tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom
  let F := (tildeEquiv (R := R)).inverse
  let e := affineQcohΓForgetIso (R := R) H
  let t := e.inv.app M ≫ (ModuleCat.restrictScalars (algebraMap R H)).map g ≫ e.hom.app N
  let f : B.qcohForget.obj M ⟶ B.qcohForget.obj N := F.preimage t
  refine ⟨f.hom, ?_⟩
  intro m
  have hf : F.map f = t := F.map_preimage t
  have h := congrArg (fun z : F.obj (B.qcohForget.obj M) ⟶
    F.obj (B.qcohForget.obj N) => z.hom m) hf
  change (f.hom.val.app (.op ⊤)).hom m = g.hom m at h
  exact h

/--
概要：アフィン上の準連接係数加群層の大域切断関手は充満。
方針：基礎 O 加群層の射を通常の tilde 同値で戻し、定数作用との可換性から係数線形にする。
規約：大域切断の H 線形性を用い、終域の切断上の写像は変更しない。
使われ方：KST D4・T1′、Toën §3.2 のアフィン係数同値への入力。
-/
instance affineQcohΓ_full : (affineQcohΓ (R := R) H).Full where
  map_surjective {M N} g := by
    let B := tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom
    obtain ⟨φ, hφ⟩ := affineUnderlyingHom_lift H M N g
    let : (B.forget.obj M.obj).IsQuasicoherent := M.property
    have hlin : ∀ h : H, ∀ m : M.obj.val.obj (.op ⊤),
        (φ.val.app (.op ⊤)).hom
          ((tensorCoefficientConstant H (Scheme.ΓSpecIso R).inv.hom).app (.op ⊤) h • m) =
        (tensorCoefficientConstant H (Scheme.ΓSpecIso R).inv.hom).app (.op ⊤) h •
          (show N.obj.val.obj (.op ⊤) from (φ.val.app (.op ⊤)).hom m) := by
      intro h m
      rw [hφ, hφ]
      exact g.hom.map_smul h m
    let f : M.obj ⟶ N.obj := coefficientHomOfCommutes H (Scheme.ΓSpecIso R).inv.hom φ
      (affineUnderlyingHom_commutesConstant H φ hlin)
    refine ⟨ObjectProperty.homMk f, ?_⟩
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    change (φ.val.app (.op ⊤)).hom m = g.hom m
    exact hφ m

end SerrePositivity.KST.DerivedGeometry
