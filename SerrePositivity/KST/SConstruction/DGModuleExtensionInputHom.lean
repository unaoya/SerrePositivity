module
public import SerrePositivity.KST.SConstruction.DGFunctorGraphLeftHom
public import SerrePositivity.KST.SConstruction.LeftTensorParameterFactorization
public import SerrePositivity.KST.SConstruction.DGModuleExtensionParameter

/-! # 元の入力 Hom の実加群延長への作用と評価因子化
概要：元の入力 Hom から実加群間の Hom への作用を、同じ実 tensor 写像で計算する。
方針：graph の左加群 Hom 表示と、任意パラメータの実左 tensor 因子化を使う。
規約：全加群型の end を作らない。使われ方：実延長の入力 Hom 合成保存。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Opposite SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w)
  [DGCategory A D] [Small.{u} D] [DGCategory A E] [Small.{u} E]
  (F G : DGFunctor A D E)

/-- 普遍入力パラメータの graph 左 Hom 表示は、元の二回の後合成と比較の作用。 -/
lemma dgFunctorGraphLeftParameterHom (e : E) :
    dgLeftModuleParameterHom A D (Bimodule.paramLeftAt A E D
      (dgFunctorGraphParameter A D E
        (dgFunctorHomEquiv A D E (dgFunctorHom A D E F G) F G (𝟙 _))) e) =
      dgFunctorGraphLeftHom A D E F G e := by
  apply moduleHom_ext
  intro d
  change _ ≫ leftModuleHomπ A D ((functorGraph A D E F).leftAt e)
      ((functorGraph A D E G).leftAt e) d.unop =
    _ ≫ leftModuleHomπ A D ((functorGraph A D E F).leftAt e)
      ((functorGraph A D E G).leftAt e) d.unop
  rw [dgLeftModuleParameterHom_π, dgFunctorGraphLeftHom_π]
  change ((𝟙 _ ≫ dgFunctorHomπ A D E F G d.unop) ≫
      yonedaHom A E (F.obj d.unop) (G.obj d.unop)) ≫ _ = _
  simp only [Category.id_comp, Category.assoc]
  rfl

/-- 元の入力 Hom から、同じ実加群延長間の全 Hom への chain map。 -/
def dgModuleExtensionInputHom (M : RightModule A D) :
    dgFunctorHom A D E F G ⟶ moduleHom A E
      ((dgModuleExtension A D E F).obj M) ((dgModuleExtension A D E G).obj M) :=
  (dgModuleExtensionParameter A D E
    (dgFunctorHomEquiv A D E (dgFunctorHom A D E F G) F G (𝟙 _))).app M

/-- 実加群延長の入力 Hom の作用は、評価後に元の左 tensor Hom 写像を通る。 -/
lemma dgModuleExtensionInputHom_π (M : RightModule A D) (e : E) :
    dgModuleExtensionInputHom A D E F G M ≫ moduleHomπ A E
        ((dgModuleExtension A D E F).obj M) ((dgModuleExtension A D E G).obj M) e =
      dgFunctorGraphLeftHom A D E F G e ≫ BalancedTensor.leftHomMap A D M
        ((functorGraph A D E F).leftAt e) ((functorGraph A D E G).leftAt e) := by
  rw [dgModuleExtensionInputHom, dgModuleExtensionParameter_π]
  exact (dgLeftParamHom_factorization A D M (Bimodule.paramLeftAt A E D
    (dgFunctorGraphParameter A D E
      (dgFunctorHomEquiv A D E (dgFunctorHom A D E F G) F G (𝟙 _))) e)).trans
    (congrArg (fun k => k ≫ BalancedTensor.leftHomMap A D M
      ((functorGraph A D E F).leftAt e) ((functorGraph A D E G).leftAt e))
        (dgFunctorGraphLeftParameterHom A D E F G e))

end SerrePositivity.KST.SConstruction
