module

public import SerrePositivity.KST.DerivedGeometry.AffineTensorComparison
public import SerrePositivity.KST.DerivedGeometry.CoefficientTensorPresheaf

/-!
# アフィン係数前層の加法的模型

概要：係数環前層を加法群へ忘れたものと、加群テンソル前層を同定する。
方針：Spec R の切断の代数構造の一致でテンソル積のスカラー作用を揃える。
規約：H の乗法の可換性は要求しない。
使われ方：KST D4、Toën Derived Azumaya §3.2 の環層と tilde の比較。
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

variable {R : CommRingCat.{u}} (H : Type u) [Ring H] [Algebra R H]

/--
概要：切断のスカラー構造を指定したテンソル積の基礎加法群。
方針：代数構造を明示的な引数として保持する。
規約：異なる代数構造の比較に使う。
使われ方：KST D4、Toën §3.2 のアフィンの係数テンソルの移送。
-/
def affineTensorAdditiveObject (U : (Spec R).Opens) (S : Algebra R Γ(Spec R, U)) :
    AddCommGrpCat.{u} := by
  letI := S
  letI : Module R Γ(Spec R, U) := Algebra.toModule
  exact AddCommGrpCat.of (H ⊗[R] Γ(Spec R, U))

/--
概要：スカラー構造を指定した加法的テンソルの純テンソル。
方針：指定された代数構造の加群作用を明示して構成する。
規約：比較の両側のスカラー構造を混在させない。
使われ方：KST D4、Toën §3.2 のアフィン前層比較の計算。
-/
def affineTensorAdditivePure (U : (Spec R).Opens) (S : Algebra R Γ(Spec R, U))
    (h : H) (s : Γ(Spec R, U)) : affineTensorAdditiveObject H U S := by
  letI := S
  letI : Module R Γ(Spec R, U) := Algebra.toModule
  exact h ⊗ₜ[R] s

/--
概要：代数構造の等式による移送は純テンソルの値と可換。
方針：等式による帰納で同一の構造へ帰着する。
規約：加法群の同一視の計算式。
使われ方：KST D4、Toën §3.2 の作用の明示的な移送。
-/
lemma affineTensorAdditivePure_cast (U : (Spec R).Opens)
    {S T : Algebra R Γ(Spec R, U)} (e : S = T) (h : H) (s : Γ(Spec R, U)) :
    (eqToHom (congrArg (affineTensorAdditiveObject H U) e))
      (affineTensorAdditivePure H U S h s) = affineTensorAdditivePure H U T h s := by
  cases e
  rfl

/--
概要：指定スカラー構造のテンソルからの加法的な射を純テンソルで判定する。
方針：テンソル積の加法による帰納を使う。
規約：値域の加法群にスカラー作用は要求しない。
使われ方：KST D4、Toën §3.2 の前層比較の自然性。
-/
lemma affineTensorAdditiveObject_hom_ext (U : (Spec R).Opens) (S : Algebra R Γ(Spec R, U))
    {N : AddCommGrpCat.{u}} {f g : affineTensorAdditiveObject H U S ⟶ N}
    (hfg : ∀ h s, f (affineTensorAdditivePure H U S h s) =
      g (affineTensorAdditivePure H U S h s)) : f = g := by
  let := S
  let : Module R Γ(Spec R, U) := Algebra.toModule
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul h s => exact hfg h s
  | add x y hx hy => simp only [map_add, hx, hy]

/--
概要：各開で係数環のテンソルと標準的な加群テンソルの基礎加法群を同定する。
方針：同じ切断環の二つのスカラー作用の一致を使う。
規約：H の非可換性を許す。
使われ方：KST D4、Toën §3.2 の環前層と加群前層の比較。
-/
def affineCoefficientAdditiveIsoAt (U : (Spec R).Opens) :
    ((coefficientTensorPresheaf H (Scheme.ΓSpecIso R).inv.hom) ⋙
      forget₂ RingCat AddCommGrpCat).obj (.op U) ≅
    (affineModuleTensorPresheaf (ModuleCat.of R H) ⋙
      forget₂ (ModuleCat.{u} R) AddCommGrpCat).obj (.op U) := by
  change affineTensorAdditiveObject H U (sectionAlgebra (Scheme.ΓSpecIso R).inv.hom U) ≅
    affineTensorAdditiveObject H U (inferInstance : Algebra R Γ(Spec R, U))
  exact eqToIso (congrArg (affineTensorAdditiveObject H U) (sectionAlgebra_spec R U))

/--
概要：係数前層と加群前層の各開の同型は純テンソルを保つ。
方針：代数構造の等式による移送の計算式を使う。
規約：両側の作用を明示的に指定する。
使われ方：KST D4、Toën §3.2 の自然な係数前層比較。
-/
lemma affineCoefficientAdditiveIsoAt_pure (U : (Spec R).Opens) (h : H)
    (s : Γ(Spec R, U)) :
    (affineCoefficientAdditiveIsoAt H U).hom
        (affineTensorAdditivePure H U (sectionAlgebra (Scheme.ΓSpecIso R).inv.hom U) h s) =
      affineTensorAdditivePure H U (inferInstance : Algebra R Γ(Spec R, U)) h s :=
  affineTensorAdditivePure_cast H U (sectionAlgebra_spec R U) h s

/--
概要：係数環前層の制限は指定した純テンソルを制限した純テンソルに送る。
方針：テンソル積の写像の純テンソル計算を使う。
規約：構造射は Spec R の標準のもの。
使われ方：KST D4、Toën §3.2 のアフィン係数前層の自然性。
-/
lemma affineCoefficientPresheaf_map_pure {U V : (Spec R).Opens} (i : U ⟶ V)
    (h : H) (s : Γ(Spec R, V)) :
    (coefficientTensorPresheaf H (Scheme.ΓSpecIso R).inv.hom).map i.op
        (affineTensorAdditivePure H V (sectionAlgebra (Scheme.ΓSpecIso R).inv.hom V) h s) =
      affineTensorAdditivePure H U (sectionAlgebra (Scheme.ΓSpecIso R).inv.hom U)
        h ((Spec R).presheaf.map i.op s) := rfl

/--
概要：標準的な加群テンソル前層の制限は純テンソルを保つ。
方針：線形写像のテンソルの計算を使う。
規約：各開の標準の代数構造を使う。
使われ方：KST D4、Toën §3.2 の加法的比較の自然性。
-/
lemma affineModuleTensorPresheaf_map_pure {U V : (Spec R).Opens} (i : U ⟶ V)
    (h : H) (s : Γ(Spec R, V)) :
    (affineModuleTensorPresheaf (ModuleCat.of R H)).map i.op
        (affineTensorAdditivePure H V (inferInstance : Algebra R Γ(Spec R, V)) h s) =
      affineTensorAdditivePure H U (inferInstance : Algebra R Γ(Spec R, U))
        h ((Spec R).presheaf.map i.op s) := rfl

/--
概要：アフィンの係数環前層と加群テンソル前層の基礎加法群の自然同型。
方針：各開で作用を揃えた同型を取り、純テンソルで自然性を証明する。
規約：H の可換性・平坦性は不要。
使われ方：KST D4、Toën §3.2 の具体的係数環層と tilde の接続。
-/
def affineCoefficientAdditiveIso :
    coefficientTensorPresheaf H (Scheme.ΓSpecIso R).inv.hom ⋙
      forget₂ RingCat AddCommGrpCat ≅
    affineModuleTensorPresheaf (ModuleCat.of R H) ⋙
      forget₂ (ModuleCat.{u} R) AddCommGrpCat :=
  NatIso.ofComponents (fun U => affineCoefficientAdditiveIsoAt H U.unop) (fun {U V} i => by
    apply affineTensorAdditiveObject_hom_ext H U.unop
      (sectionAlgebra (Scheme.ΓSpecIso R).inv.hom U.unop)
    intro h s
    change (affineCoefficientAdditiveIsoAt H V.unop).hom
        ((coefficientTensorPresheaf H (Scheme.ΓSpecIso R).inv.hom).map i
          (affineTensorAdditivePure H U.unop
            (sectionAlgebra (Scheme.ΓSpecIso R).inv.hom U.unop) h s)) =
      (affineModuleTensorPresheaf (ModuleCat.of R H)).map i
        ((affineCoefficientAdditiveIsoAt H U.unop).hom
          (affineTensorAdditivePure H U.unop
            (sectionAlgebra (Scheme.ΓSpecIso R).inv.hom U.unop) h s))
    erw [affineCoefficientPresheaf_map_pure H i.unop h s,
      affineCoefficientAdditiveIsoAt_pure H V.unop,
      affineCoefficientAdditiveIsoAt_pure H U.unop,
      affineModuleTensorPresheaf_map_pure H i.unop])

end SerrePositivity.KST.DerivedGeometry
