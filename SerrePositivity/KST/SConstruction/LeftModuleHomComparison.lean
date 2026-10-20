module
public import SerrePositivity.KST.SConstruction.LeftModuleParameterRepresentation
public import SerrePositivity.KST.SConstruction.DGFunctorEnrichment

/-! # 関手 Hom end から既存の左加群 Hom への比較
概要：元の全次数自然変換を、既存の左加群 Hom へ単位・合成を保って移す。
方針：全対象評価で両 Hom の単位・合成を同じ複体上の演算へ帰着する。
規約：二つの豊穣構造を同一視しない。使われ方：実 tensor 高次作用の合成保存。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Opposite SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 元の関手 Hom end の全対象評価を保持する、既存の左加群 Hom への chain map。 -/
def dgLeftModuleHomComparison (N N' : LeftModule A D) :
    dgFunctorHom A D (Complex A) N N' ⟶ leftModuleHom A D N N' :=
  dgLeftModuleParameterHom A D
    (dgFunctorHomEquiv A D (Complex A) (dgFunctorHom A D (Complex A) N N') N N' (𝟙 _))

/-- 比較後の評価は、元の同じ対象における Hom end の評価。 -/
lemma dgLeftModuleHomComparison_π (N N' : LeftModule A D) (d : D) :
    dgLeftModuleHomComparison A D N N' ≫ leftModuleHomπ A D N N' d =
      dgFunctorHomπ A D (Complex A) N N' d := by
  rw [dgLeftModuleHomComparison, dgLeftModuleParameterHom_π]
  exact Category.id_comp _

/-- 任意パラメータの既存 Hom 表示は、元の関手 Hom の表示と同じ比較の合成。 -/
lemma dgLeftModuleParameterHom_comparison {K : Complex A} {N N' : LeftModule A D}
    (τ : DGFunctorParamTrans A D (Complex A) K N N') :
    dgLeftModuleParameterHom A D τ =
      (dgFunctorHomEquiv A D (Complex A) K N N').symm τ ≫
        dgLeftModuleHomComparison A D N N' := by
  apply moduleHom_ext
  intro d
  change _ ≫ leftModuleHomπ A D N N' d.unop = _ ≫ leftModuleHomπ A D N N' d.unop
  rw [dgLeftModuleParameterHom_π, Category.assoc, dgLeftModuleHomComparison_π,
    dgFunctorHomEquiv_symm_π]

/-- 比較は元の関手 Hom end の閉単位を既存の左加群 Hom の閉単位へ送る。 -/
lemma dgLeftModuleHomComparison_identity (N : LeftModule A D) :
    dgFunctorIdentity A D (Complex A) N ≫ dgLeftModuleHomComparison A D N N =
      moduleIdentity A Dᵒᵖ N.toRightOpposite := by
  apply moduleHom_ext
  intro d
  change _ ≫ leftModuleHomπ A D N N d.unop = _ ≫ leftModuleHomπ A D N N d.unop
  rw [Category.assoc, dgLeftModuleHomComparison_π, dgFunctorIdentity_π, moduleIdentity_π]
  rfl

/-- 比較は元の全 Hom 合成を既存の左加群 Hom の合成へ送る。 -/
lemma dgLeftModuleHomComparison_composition (N N' P : LeftModule A D) :
    dgFunctorComposition A D (Complex A) N N' P ≫ dgLeftModuleHomComparison A D N P =
      (dgLeftModuleHomComparison A D N N' ⊗ₘ dgLeftModuleHomComparison A D N' P) ≫
        moduleComposition A Dᵒᵖ N.toRightOpposite N'.toRightOpposite P.toRightOpposite := by
  apply moduleHom_ext
  intro d
  change _ ≫ leftModuleHomπ A D N P d.unop = _ ≫ leftModuleHomπ A D N P d.unop
  rw [Category.assoc, dgLeftModuleHomComparison_π, dgFunctorComposition_π,
    Category.assoc, moduleComposition_π, tensorHom_comp_tensorHom_assoc,
    dgLeftModuleHomComparison_π, dgLeftModuleHomComparison_π]
  rfl

end SerrePositivity.KST.SConstruction
