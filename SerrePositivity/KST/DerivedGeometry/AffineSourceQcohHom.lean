module

public import SerrePositivity.KST.DerivedGeometry.AdjunctionSourceHom
public import SerrePositivity.KST.DerivedGeometry.AffineCoefficientFull
public import SerrePositivity.KST.DerivedGeometry.AffineCoefficientTildeFunctor

/-!
概要：準連接な始域から任意の係数加群層への射の大域切断による表示。
方針：通常の tilde–Γ 随伴で基礎射を作り、定数係数作用との可換性で係数線形にする。
規約：終域の準連接性を要求しない。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の全層へのアフィン随伴。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits AlgebraicGeometry
namespace SerrePositivity.KST.DerivedGeometry
variable {R : CommRingCat.{u}} (H : Type u) [Ring H] [Algebra R H]

/--
概要：準連接な始域の大域切断の H 線形射を任意の終域への基礎 O 加群層の射へ持ち上げる。
方針：通常の tilde–Γ 随伴の始域の余単位同型と基礎切断の比較を使う。
規約：終域の準連接性は不要。
使われ方：TT §3、Toën §3.2 の全係数加群層への随伴。
-/
lemma affineUnderlyingHom_lift_of_sourceQC
    (M : (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).QCoh)
    (N : (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).Modules)
    (g : (affineCoefficientΓ H).obj M.obj ⟶ (affineCoefficientΓ H).obj N) :
    ∃ φ : (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).forget.obj M.obj ⟶
        (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).forget.obj N,
      ∀ m : M.obj.val.obj (.op ⊤), (φ.val.app (.op ⊤)).hom m = g.hom m := by
  let B := tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom
  let : (B.forget.obj M.obj).IsQuasicoherent := M.property
  let e := affineCoefficientΓForgetIso (R := R) H
  let t := e.inv.app M.obj ≫ (ModuleCat.restrictScalars (algebraMap R H)).map g ≫ e.hom.app N
  have : IsIso ((tilde.adjunction (R := R)).counit.app (B.forget.obj M.obj)) := by
    change IsIso (Scheme.Modules.fromTildeΓ (B.forget.obj M.obj))
    infer_instance
  obtain ⟨φ, hφ⟩ := (adjunction_rightHom_bijective_of_counitIso (tilde.adjunction (R := R))
    (B.forget.obj M.obj) (B.forget.obj N)).surjective t
  refine ⟨φ, ?_⟩
  intro m
  have h := congrArg (fun z : moduleSpecΓFunctor.obj (B.forget.obj M.obj) ⟶
    moduleSpecΓFunctor.obj (B.forget.obj N) => z.hom m) hφ
  change (φ.val.app (.op ⊤)).hom m = g.hom m at h
  exact h

/--
概要：準連接な始域から任意の終域への係数加群層の射は H 大域切断で一意に決まる。
方針：基礎 O 加群層の射の大域切断による検出と係数忘却の忠実性を使う。
規約：大域切断が全層圏で忠実だとは要求しない。
使われ方：TT §3、Toën §3.2 のアフィン随伴の Hom の単射性。
-/
lemma affineCoefficientΓ_sourceQC_injective
    (M : (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).QCoh)
    (N : (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).Modules) :
    Function.Injective ((affineCoefficientΓ H).map : (M.obj ⟶ N) → _) := by
  let B := tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom
  let : (B.forget.obj M.obj).IsQuasicoherent := M.property
  intro f g h
  apply B.forget.map_injective
  apply affineUnderlyingHom_ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  have hm := congrArg (fun k => k.hom m) h
  exact hm

/--
概要：準連接な始域の大域切断の H 線形射は任意の終域への係数加群層の射へ戻せる。
方針：基礎射を持ち上げ、H 線形性から定数作用との可換性を得て係数線形にする。
規約：H の平坦性・可換性は要求しない。
使われ方：TT §3・§8、Toën §3.2 のアフィン随伴の Hom の全射性。
-/
lemma affineCoefficientΓ_sourceQC_surjective
    (M : (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).QCoh)
    (N : (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).Modules) :
    Function.Surjective ((affineCoefficientΓ H).map : (M.obj ⟶ N) → _) := by
  let B := tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom
  let : (B.forget.obj M.obj).IsQuasicoherent := M.property
  intro g
  obtain ⟨φ, hφ⟩ := affineUnderlyingHom_lift_of_sourceQC H M N g
  have hlin : ∀ h : H, ∀ m : M.obj.val.obj (.op ⊤),
      (φ.val.app (.op ⊤)).hom
        ((tensorCoefficientConstant H (Scheme.ΓSpecIso R).inv.hom).app (.op ⊤) h • m) =
      (tensorCoefficientConstant H (Scheme.ΓSpecIso R).inv.hom).app (.op ⊤) h •
        (show N.val.obj (.op ⊤) from (φ.val.app (.op ⊤)).hom m) := by
    intro h m
    rw [hφ, hφ]
    exact g.hom.map_smul h m
  let f := coefficientHomOfCommutes H (Scheme.ΓSpecIso R).inv.hom φ
    (affineUnderlyingHom_commutesConstant H φ hlin)
  refine ⟨f, ?_⟩
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  exact hφ

/--
概要：準連接な始域から任意の係数加群層への Hom は H 大域切断の Hom と同値。
方針：実際の大域切断の射写像の単射性と全射性を束ねる。
規約：同値の順写像は元の大域切断の写像。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の全層への tilde 随伴。
-/
def affineCoefficientHomEquiv_of_sourceQC
    (M : (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).QCoh)
    (N : (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).Modules) :
    (M.obj ⟶ N) ≃ ((affineCoefficientΓ H).obj M.obj ⟶ (affineCoefficientΓ H).obj N) :=
  Equiv.ofBijective (affineCoefficientΓ H).map
    ⟨affineCoefficientΓ_sourceQC_injective H M N, affineCoefficientΓ_sourceQC_surjective H M N⟩

end SerrePositivity.KST.DerivedGeometry
