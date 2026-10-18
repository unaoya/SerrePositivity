module

public import SerrePositivity.KST.DerivedGeometry.AffineTensorSections
public import Mathlib.LinearAlgebra.TensorProduct.Lift

/-!
# アフィン上のテンソル前層から tilde への自然な比較

概要：すべての開で M ⊗_R O(U) から tilde M の切断への写像を構成する。
方針：標準切断への写像を構造層の作用で線形に延長する。
規約：基本開での同型と、一般の開での比較写像を区別する。
使われ方：KST D4・T1′、Bondal–van den Bergh Thm 3.1.1、Toën §3.2 のアフィン比較。
-/

@[expose] public section

noncomputable section

set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped TensorProduct

namespace SerrePositivity.KST.DerivedGeometry

variable {R : CommRingCat.{u}}

/--
概要：Spec R の構造層の制限を標準的な R 代数準同型として表す。
方針：大域切断からの基礎環の作用と制限の両立を使う。
規約：Mathlib の標準代数構造を用いる。
使われ方：KST D4、Toën §3.2 のアフィンのテンソル前層の制限。
-/
def affineSectionRestriction {U V : (Spec R).Opens} (i : U ⟶ V) :
    Γ(Spec R, V) →ₐ[R] Γ(Spec R, U) where
  __ := (Spec R).presheaf.map i.op |>.hom
  commutes' r := congrArg (fun g : R →+* Γ(Spec R, U) => g r)
    (restriction_comp_sectionBaseMap (Scheme.ΓSpecIso R).inv.hom i)

/--
概要：M と構造層の切断のテンソルから tilde M の切断への線形写像。
方針：標準切断への R 線形写像を構造層の切断で底変換する。
規約：任意の開で構成し、平坦性や有限性を仮定しない。
使われ方：KST D4、Toën §3.2 の層化と tilde の比較。
-/
def affineTensorSectionMap (M : ModuleCat.{u} R) (U : (Spec R).Opens) :
    M ⊗[R] Γ(Spec R, U) →ₗ[R] Γ(tilde M, U) :=
  ((LinearMap.liftBaseChange Γ(Spec R, U)
    (show M →ₗ[R] Γ(tilde M, U) from (tilde.toOpen M U).hom)).restrictScalars R).comp
      (TensorProduct.comm R M Γ(Spec R, U)).toLinearMap

/--
概要：比較写像は m ⊗ s を s 倍した m の標準切断に送る。
方針：線形写像の底変換の純テンソル計算を使う。
規約：構造層の作用を右因子に記す。
使われ方：KST D4、Toën §3.2 の制限との自然性。
-/
lemma affineTensorSectionMap_tmul (M : ModuleCat.{u} R) (U : (Spec R).Opens)
    (m : M) (s : Γ(Spec R, U)) :
    affineTensorSectionMap M U (m ⊗ₜ[R] s) =
      s • (show Γ(tilde M, U) from (tilde.toOpen M U).hom m) := rfl

/--
概要：比較写像は開集合の制限と可換。
方針：純テンソルに帰着し、加群層の制限と標準切断の自然性を使う。
規約：比較写像を定義するすべての開についての主張。
使われ方：KST D4、Toën §3.2 のアフィン比較の前層射。
-/
lemma affineTensorSectionMap_naturality (M : ModuleCat.{u} R)
    {U V : (Spec R).Opens} (i : U ⟶ V) (x : M ⊗[R] Γ(Spec R, V)) :
    (tilde M).presheaf.map i.op (affineTensorSectionMap M V x) =
      affineTensorSectionMap M U
        (TensorProduct.map LinearMap.id (affineSectionRestriction i).toLinearMap x) := by
  induction x using TensorProduct.inductionOn with
  | tmul m s =>
    simp only [affineTensorSectionMap_tmul, TensorProduct.map_tmul, LinearMap.id_apply]
    rw [Scheme.Modules.map_smul]
    change (Spec R).presheaf.map i.op s •
        (tilde M).presheaf.map i.op ((tilde.toOpen M V).hom m) =
      (Spec R).presheaf.map i.op s • (show Γ(tilde M, U) from (tilde.toOpen M U).hom m)
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/--
概要：アフィン上で M ⊗_R O(U) を値に持つ R 加群の前層。
方針：構造層の R 線形な制限をテンソルする。
規約：層条件はまだ主張しない。
使われ方：KST D4、Toën §3.2 のテンソル前層のアフィン比較。
-/
def affineModuleTensorPresheaf (M : ModuleCat.{u} R) :
    TopCat.Presheaf (ModuleCat.{u} R) (Spec R) where
  obj U := ModuleCat.of R (M ⊗[R] Γ(Spec R, U.unop))
  map i := ModuleCat.ofHom
    (TensorProduct.map LinearMap.id (affineSectionRestriction i.unop).toLinearMap)
  map_id U := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul m s =>
      change (m ⊗ₜ[R] ((Spec R).presheaf.map (𝟙 U)).hom s :
        M ⊗[R] Γ(Spec R, U.unop)) = m ⊗ₜ[R] s
      rw [(Spec R).presheaf.map_id]
      rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  map_comp {U V W} i j := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul m s =>
      change (m ⊗ₜ[R] ((Spec R).presheaf.map (i ≫ j)).hom s :
        M ⊗[R] Γ(Spec R, W.unop)) =
        (m ⊗ₜ[R] ((Spec R).presheaf.map j).hom (((Spec R).presheaf.map i).hom s) :
          M ⊗[R] Γ(Spec R, W.unop))
      rw [(Spec R).presheaf.map_comp]
      rfl
    | add x y hx hy => simp only [map_add, hx, hy]

/--
概要：アフィンの加群テンソル前層から tilde M の基礎 R 加群層への自然変換。
方針：切断ごとの比較と制限への自然性をまとめる。
規約：R 線形な前層射として構成する。
使われ方：KST D4、Toën §3.2 の層化の比較射。
-/
def affineTensorToTilde (M : ModuleCat.{u} R) :
    affineModuleTensorPresheaf M ⟶ (modulesSpecToSheaf.obj (tilde M)).obj where
  app U := (show ModuleCat.of R (M ⊗[R] Γ(Spec R, U.unop)) ⟶
      ModuleCat.of R Γ(tilde M, U.unop) from
    ModuleCat.ofHom (affineTensorSectionMap M U.unop))
  naturality {U V} i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (affineTensorSectionMap_naturality M i.unop x).symm

/--
概要：比較写像は基本開上で前に構成した局所化の同型と一致する。
方針：純テンソルでの同じ計算式により線形写像を同定する。
規約：基本開上での局所化の選択に依存しない比較を使う。
使われ方：KST D4、Toën §3.2 の基本開上の同型判定。
-/
lemma affineTensorSectionMap_basic (M : ModuleCat.{u} R) (f : R) :
    affineTensorSectionMap M (PrimeSpectrum.basicOpen f) =
      (affineBasicTensorSectionsEquiv M f).toLinearMap := by
  ext m s
  exact (affineBasicTensorSectionsEquiv_tmul M f m s).symm

/--
概要：アフィンの前層比較は基本開の各成分で同型。
方針：比較写像を局所化の線形同型に同定する。
規約：任意の R 加群に対する主張。
使われ方：KST D4、Toën §3.2 の層化後のアフィン比較。
-/
instance affineTensorToTilde_basic_isIso (M : ModuleCat.{u} R) (f : R) :
    IsIso ((affineTensorToTilde M).app (.op (PrimeSpectrum.basicOpen f))) := by
  change IsIso (ModuleCat.ofHom (affineTensorSectionMap M (PrimeSpectrum.basicOpen f)))
  rw [affineTensorSectionMap_basic]
  exact (LinearEquiv.toModuleIso (affineBasicTensorSectionsEquiv M f)).isIso_hom

end SerrePositivity.KST.DerivedGeometry
