module

public import SerrePositivity.HomologicalAlgebra.UnderNerveWeight
public import SerrePositivity.HomologicalAlgebra.UnderChainEquiv
public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
import all SerrePositivity.HomologicalAlgebra.UnderNerveWeight
import all SerrePositivity.HomologicalAlgebra.UnderChainEquiv

/-!
# 係数付き bar 重みの各項の射影性

## 概要
射影係数を持つ bar 重みの各単体次数は、前層圏で射影的である。

## 方針
底の各射列の標準 under 持ち上げで係数を持ち上げ、先頭の構造射で全生成元へ自然に延ばす。

## 規約
元の全射列と係数を保持する。各評価の射影性だけで前層の射影性を推論しない。

## 使われ方
Weibel §2.2、HA 1.2.4。標準単体の重みとの実際の射影分解の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
namespace SerrePositivity.HomologicalAlgebra
variable (J : Type) [SmallCategory J]
variable {C : Type u} [Category.{v} C] [HasCoproducts.{0} C] [HasPushouts C]

/-- 射影係数のとき、bar 重みの各単体次数は前層圏で射影的。 -/
theorem coefficientBarWeight_projective (P : C) [Projective P] (n : SimplexCategoryᵒᵖ) :
    Projective ((coefficientBarWeight J P).obj n) where
  factors {E F} φ p _ := by
    have hg (s : ComposableArrows J n.unop.len) :
        ∃ g : P ⟶ E.obj (op (s.obj 0)), g ≫ p.app (op (s.obj 0)) =
          coefficientBarWeightι J P n (op (s.obj 0)) (underScaffold s) ≫
            φ.app (op (s.obj 0)) := by
      have : Epi (p.app (op (s.obj 0))) := inferInstance
      exact Projective.factors _ _
    choose g hg using hg
    let ℓ : (coefficientBarWeight J P).obj n ⟶ E :=
      { app x := Sigma.desc (fun τ => g (τ ⋙ Under.forget x.unop) ≫ E.map (τ.obj 0).hom.op)
        naturality {x y} f := by
          apply Sigma.hom_ext
          intro τ
          change coefficientBarWeightι J P n x τ ≫
            (((coefficientBarWeight J P).obj n).map f ≫ _) = _
          rw [coefficientBarWeightι_map_assoc]
          simp only [coefficientBarWeightι, Category.assoc, Sigma.ι_comp_desc, Sigma.ι_comp_desc_assoc]
          change g (τ ⋙ Under.forget x.unop) ≫ E.map ((f.unop ≫ (τ.obj 0).hom).op) =
            g (τ ⋙ Under.forget x.unop) ≫ E.map (τ.obj 0).hom.op ≫ E.map f
          rw [op_comp, E.map_comp]
          rfl }
    refine ⟨ℓ, ?_⟩
    apply NatTrans.ext
    funext x
    apply Sigma.hom_ext
    intro τ
    let s := τ ⋙ Under.forget x.unop
    change coefficientBarWeightι J P n x τ ≫
      (Sigma.desc (fun σ => g (σ ⋙ Under.forget x.unop) ≫ E.map (σ.obj 0).hom.op) ≫
        p.app x) = coefficientBarWeightι J P n x τ ≫ φ.app x
    rw [show coefficientBarWeightι J P n x τ ≫
        (Sigma.desc (fun σ => g (σ ⋙ Under.forget x.unop) ≫ E.map (σ.obj 0).hom.op) ≫
          p.app x) = (g s ≫ E.map (τ.obj 0).hom.op) ≫ p.app x from
      Sigma.ι_comp_desc_assoc _ _ _]
    rw [Category.assoc, p.naturality, ← Category.assoc, hg s,
      Category.assoc, ← φ.naturality, ← Category.assoc, coefficientBarWeightι_map]
    exact congrArg (fun κ => coefficientBarWeightι J P n x κ ≫ φ.app x)
      (underScaffold_factorization τ)

/-- bar の同じ増大と射影的な各項を備えた、定数係数前層の射影分解。 -/
def coefficientBarWeightResolution [Abelian C] (P : C) [Projective P] :
    ProjectiveResolution (coefficientBarWeightPoint J P) where
  complex := AlternatingFaceMapComplex.obj (coefficientBarWeight J P)
  projective n := coefficientBarWeight_projective J P (op (SimplexCategory.mk n))
  π := AlternatingFaceMapComplex.ε.app (coefficientBarWeightAugmented J P)
  quasiIso := coefficientBarWeight_augmentation_quasiIso J P

end SerrePositivity.HomologicalAlgebra
