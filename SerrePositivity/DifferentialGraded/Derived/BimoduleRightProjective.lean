module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleRestrictionProjective
public import SerrePositivity.DifferentialGraded.Derived.FreeProjective
public import SerrePositivity.DifferentialGraded.Bimodule.Right
public import SerrePositivity.DifferentialGraded.Complexes.KProjectiveTensor
public import SerrePositivity.DifferentialGraded.Complexes.SphereHom

/-!
概要：相手側 Hom の K-projective 性から同じ semifree bimodule 解像度の右射影性。
方針：生成 sphere の制限を K-projective 係数の自由加群へ同型で比較する。
規約：K-flat 性だけを使う相対平坦性とは区別する。
使われ方：標準 cell source 上の固定 graph 解像度。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B] [Small.{u} C]

lemma restrictedFree_homotopicallyProjective
    (hC : ∀ x y : C, (homObject A C x y).IsKProjective)
    (b₀ : B) (c₀ c : C) (K : Complex A) [K.IsKProjective] :
    moduleHomotopicallyProjective A B
      ((tensorRightRestriction A B C c).obj
        ((freeAt (A := A) (D := (DGTensorCategory A Bᵒᵖ C)ᵒᵖ)
          (op ((op b₀, c₀) : DGTensorCategory A Bᵒᵖ C))).obj K)) := by
  let := hC c₀ c
  let := complexTensor_isKProjective A K (homObject A C c₀ c)
  exact moduleHomotopicallyProjective_of_iso A B (restrictedFreeIso A B C b₀ c₀ c K).symm
    (freeAt_homotopicallyProjective A B b₀ _)

lemma BimoduleSemifreeResolution.right_homotopicallyProjective
    (hC : ∀ x y : C, (homObject A C x y).IsKProjective)
    {M : BimoduleCategory A B C} (P : BimoduleSemifreeResolution A B C M) (c : C) :
    moduleHomotopicallyProjective A B ((BimoduleCategory.evaluation A B C c).obj P.obj) := by
  apply P.right_homotopicallyProjective_of_cells A B C
  intro c x n
  let := isKProjective_of_homComplex_acyclic A (complexSphere A n)
    (fun _ hN => complexSphereHom_acyclic A _ n hN)
  exact restrictedFree_homotopicallyProjective A B C hC x.unop.1.unop x.unop.2 c
    (complexSphere A n)

end SerrePositivity.DifferentialGraded
