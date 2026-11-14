module

public import SerrePositivity.EInfinity.SimplexCuts.Normalization

/-!
# 元の係数基底と正規化生成元による双線形成分の外延性

Berger–Fresse §1.1.4・§2.2.7、M14 L10の証明分割。
既存の自由基底とgenerator_hom_extを同じ双線形族に適用する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- C303：係数の元の自由基底と正規化生成元で一致する双線形族は等しい。 -/
lemma normalized_bilinear_ext (S : SSet.{0}) {n d q : ℕ} {M : ModuleCat.{u} A}
    (f g : Surjection.degreeModule A n d →ₗ[A] (AlexanderWhitney.chains A S).X q →ₗ[A] M)
    (h : ∀ (w : Surjection.BasisWord n d) (x : S _⦋q⦌),
      f (Surjection.basis A n d (ULift.up w)) (AlexanderWhitney.generator A S q x) =
        g (Surjection.basis A n d (ULift.up w)) (AlexanderWhitney.generator A S q x)) :
    f = g := by
  apply (Surjection.basis A n d).ext
  intro w
  rcases w with ⟨w⟩
  have he : ModuleCat.ofHom (f (Surjection.basis A n d (ULift.up w))) =
      ModuleCat.ofHom (g (Surjection.basis A n d (ULift.up w))) :=
    AlexanderWhitney.generator_hom_ext A S q (fun x => h w x)
  exact congrArg ModuleCat.Hom.hom he

end SerrePositivity.EInfinity.SimplexCuts
