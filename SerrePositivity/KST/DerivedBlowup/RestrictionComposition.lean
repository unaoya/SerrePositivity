module

public import SerrePositivity.DifferentialGraded.Tensor.ScalarRestrictionCategory

/-!
概要：KST §3.1 の dg チャート図式で使う、係数制限の合成比較。
方針：加群の標準合成同型を複体へ持ち上げ、単位と tensor の成分で整合性を確認する。
規約：既存の係数制限と豊穣構造を使う。
使われ方：異なる係数環を経由するチャート dg 遷移の合成。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory CategoryTheory.MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded.ScalarExtension
open scoped TensorProduct

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]

/-- 概要：二段の係数制限と合成環射による係数制限の複体自然同型。
方針：ModuleCat の合成同型を mapHomologicalComplex へ持ち上げる。
規約：KST §3.1。使われ方：dg チャートの係数環変更の合成比較。 -/
def restrictionCompositionIso (φ : A →+* B) (ψ : B →+* C) :
    restriction ψ ⋙ restriction φ ≅ restriction (ψ.comp φ) :=
  Functor.mapHomologicalComplexCompIso (ModuleCat.restrictScalarsComp φ ψ).symm (.up ℤ)

/-- 概要：係数制限の合成比較は各次数の元を変えない。
方針：加群の合成同型が恒等関数であることを使う。
規約：KST §3.1。使われ方：単位・tensor 比較の成分計算。 -/
theorem restrictionCompositionIso_hom_apply (φ : A →+* B) (ψ : B →+* C)
    (K : DifferentialGraded.Complex C) (q : ℤ) (z : K.X q) :
    (((restrictionCompositionIso φ ψ).hom.app K).f q) z = z := rfl

/-- 概要：係数制限の逆合成比較も各次数の元を変えない。
方針：加群の合成同型の逆が恒等関数であることを使う。
規約：KST §3.1。使われ方：合成比較の可逆性と各方向の dg 関手。 -/
theorem restrictionCompositionIso_inv_apply (φ : A →+* B) (ψ : B →+* C)
    (K : DifferentialGraded.Complex C) (q : ℤ) (z : K.X q) :
    (((restrictionCompositionIso φ ψ).inv.app K).f q) z = z := rfl

/-- 概要：係数制限の合成比較は tensor 構造射と可換。
方針：双次数の純粋 tensor で二段の係数制限の計算を一段へまとめる。
規約：KST §3.1。使われ方：合成比較を dg 関手へ持ち上げる乗法条件。 -/
theorem restrictionCompositionIso_tensor (φ : A →+* B) (ψ : B →+* C)
    (K L : DifferentialGraded.Complex C) :
    Functor.LaxMonoidal.μ (restriction φ) ((restriction ψ).obj K) ((restriction ψ).obj L) ≫
      (restriction φ).map (Functor.LaxMonoidal.μ (restriction ψ) K L) ≫
        (restrictionCompositionIso φ ψ).hom.app (K ⊗ L) =
    ((restrictionCompositionIso φ ψ).hom.app K ⊗ₘ
      (restrictionCompositionIso φ ψ).hom.app L) ≫
        Functor.LaxMonoidal.μ (restriction (ψ.comp φ)) K L := by
  apply DifferentialGraded.tensorHom_ext
  intro p q n hn
  simp only [comp_f, DifferentialGraded.ι_tensorHom_assoc]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  change (Functor.LaxMonoidal.μ (restriction ψ) K L).f n
      ((Functor.LaxMonoidal.μ (restriction φ) ((restriction ψ).obj K) ((restriction ψ).obj L)).f n
        (ιTensorObj ((restriction φ).obj ((restriction ψ).obj K))
          ((restriction φ).obj ((restriction ψ).obj L)) p q n hn (x ⊗ₜ[A] y))) =
    (Functor.LaxMonoidal.μ (restriction (ψ.comp φ)) K L).f n
      (ιTensorObj ((restriction (ψ.comp φ)).obj K) ((restriction (ψ.comp φ)).obj L) p q n hn
        ((((restrictionCompositionIso φ ψ).hom.app K).f p x) ⊗ₜ[A]
          (((restrictionCompositionIso φ ψ).hom.app L).f q y)))
  rw [restriction_μ_apply, restriction_μ_apply]
  rw [restrictionCompositionIso_hom_apply,
    restrictionCompositionIso_hom_apply, restriction_μ_apply]

/-- 概要：係数制限の合成比較は単位構造射と可換。
方針：単位複体からの射を次数0の1で比較し、各係数制限の単位公式を使う。
規約：KST §3.1。使われ方：合成比較を dg 関手へ持ち上げる単位条件。 -/
theorem restrictionCompositionIso_unit (φ : A →+* B) (ψ : B →+* C) :
    Functor.LaxMonoidal.ε (restriction φ) ≫
      (restriction φ).map (Functor.LaxMonoidal.ε (restriction ψ)) ≫
        (restrictionCompositionIso φ ψ).hom.app (𝟙_ (DifferentialGraded.Complex C)) =
      Functor.LaxMonoidal.ε (restriction (ψ.comp φ)) := by
  apply (DifferentialGraded.unitCycleEquiv _).injective
  apply Subtype.ext
  change (Functor.LaxMonoidal.ε (restriction ψ)).f 0
      ((Functor.LaxMonoidal.ε (restriction φ)).f 0
        ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A))) =
    (Functor.LaxMonoidal.ε (restriction (ψ.comp φ))).f 0
      ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A))
  rw [restriction_ε_one, restriction_ε_one, restriction_ε_one]

/-- 概要：二段の係数制限と合成環射による係数制限の間の dg 関手。
方針：Hom に複体の合成同型を使い、自然性と単位・tensor の整合性から圏法則を得る。
規約：KST §3.1。使われ方：係数環が変わるチャート dg 遷移の合成比較。 -/
def restrictionCompositionDGFunctor (φ : A →+* B) (ψ : B →+* C)
    (D : Type v) [DifferentialGraded.DGCategory C D] :
    DifferentialGraded.DGFunctor A (DGRestriction φ (DGRestriction ψ D))
      (DGRestriction (ψ.comp φ) D) where
  obj x := x
  map x y := (restrictionCompositionIso φ ψ).hom.app (DifferentialGraded.homObject C D x y)
  map_id x := by
    have hn := (restrictionCompositionIso φ ψ).hom.naturality
      (eId (DifferentialGraded.Complex C) (C := D) x)
    dsimp only [Functor.comp_map] at hn
    change (Functor.LaxMonoidal.ε (restriction φ) ≫
      (restriction φ).map (Functor.LaxMonoidal.ε (restriction ψ) ≫
        (restriction ψ).map (eId (DifferentialGraded.Complex C) (C := D) x))) ≫ _ =
      Functor.LaxMonoidal.ε (restriction (ψ.comp φ)) ≫
        (restriction (ψ.comp φ)).map (eId (DifferentialGraded.Complex C) (C := D) x)
    rw [Functor.map_comp, Category.assoc, Category.assoc, hn]
    simpa only [Category.assoc] using congrArg
      (fun f => f ≫ (restriction (ψ.comp φ)).map
        (eId (DifferentialGraded.Complex C) (C := D) x)) (restrictionCompositionIso_unit φ ψ)
  map_comp x y z := by
    have hn := (restrictionCompositionIso φ ψ).hom.naturality
      (eComp (DifferentialGraded.Complex C) (C := D) x y z)
    dsimp only [Functor.comp_map] at hn
    change (Functor.LaxMonoidal.μ (restriction φ)
      ((restriction ψ).obj (DifferentialGraded.homObject C D x y))
      ((restriction ψ).obj (DifferentialGraded.homObject C D y z)) ≫
      (restriction φ).map (Functor.LaxMonoidal.μ (restriction ψ) _ _ ≫
        (restriction ψ).map (eComp (DifferentialGraded.Complex C) (C := D) x y z))) ≫ _ =
      ((restrictionCompositionIso φ ψ).hom.app (DifferentialGraded.homObject C D x y) ⊗ₘ
        (restrictionCompositionIso φ ψ).hom.app (DifferentialGraded.homObject C D y z)) ≫
        Functor.LaxMonoidal.μ (restriction (ψ.comp φ)) _ _ ≫
          (restriction (ψ.comp φ)).map (eComp (DifferentialGraded.Complex C) (C := D) x y z)
    rw [Functor.map_comp, Category.assoc, Category.assoc, hn]
    simpa only [Category.assoc] using congrArg
      (fun f => f ≫ (restriction (ψ.comp φ)).map
        (eComp (DifferentialGraded.Complex C) (C := D) x y z))
      (restrictionCompositionIso_tensor φ ψ
        (DifferentialGraded.homObject C D x y) (DifferentialGraded.homObject C D y z))

/-- 概要：係数制限の合成比較 dg 関手は各 Hom 上で可逆。
方針：Hom 写像は自然同型の成分。
規約：KST §3.1。使われ方：係数制限の合成で局所 dg 同値性が変わらないこと。 -/
theorem restrictionCompositionDGFunctor_map_isIso (φ : A →+* B) (ψ : B →+* C)
    (D : Type v) [DifferentialGraded.DGCategory C D] (x y) :
    IsIso ((restrictionCompositionDGFunctor φ ψ D).map x y) := by
  change IsIso ((restrictionCompositionIso φ ψ).app (DifferentialGraded.homObject C D x y)).hom
  infer_instance

end SerrePositivity.KST.DerivedBlowup
