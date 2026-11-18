module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Normalization

/-!
模型。文献の定義との比較は後で
# 元の係数基底と正規化生成元による双線形成分の外延性

Berger–Fresse §1.1.4・§2.2.7、M14 L10の証明分割。
既存の自由基底とgenerator_hom_extを同じ双線形族に適用する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A]

/-- C303：係数の元の自由基底と正規化生成元で一致する双線形族は等しい。 -/
lemma normalized_bilinear_ext (S : SSet.{0}) {n d q : ℕ} {M : ModuleCat.{u} A}
    (f g : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeModule A n d →ₗ[A] (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A S).X q →ₗ[A] M)
    (h : ∀ (w : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) (x : S _⦋q⦌),
      f (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A n d (ULift.up w)) (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A S q x) =
        g (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A n d (ULift.up w)) (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A S q x)) :
    f = g := by
  apply (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A n d).ext
  intro w
  rcases w with ⟨w⟩
  have he : ModuleCat.ofHom (f (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A n d (ULift.up w))) =
      ModuleCat.ofHom (g (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A n d (ULift.up w))) :=
    _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator_hom_ext A S q (fun x => h w x)
  exact congrArg ModuleCat.Hom.hom he

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
