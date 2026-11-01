module
public import SerrePositivity.KST.SConstruction.LeftModuleHomComparison
public import SerrePositivity.KST.SConstruction.DGFunctorWhiskering
public import SerrePositivity.DifferentialGraded.SharedFunctoriality.DGFunctorGraphParameter

/-! # 元の入力 Hom から graph の左加群 Hom への作用
概要：dg Yoneda と値の評価で後合成し、既存の左加群 Hom へ作用を移す。
方針：二つの dg 後合成と、全 Hom の単位・合成を保つ比較を使う。
規約：関手 Hom と左加群 Hom の二つの豊穣を区別する。使われ方：実延長の合成保存。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w)
  [DGCategory A D] [Small.{u} D] [DGCategory A E] [Small.{u} E]

/-- 元の入力 Hom から、graph 左評価の関手 Hom end への二回の後合成。 -/
def dgFunctorGraphLeftEnd (F G : DGFunctor A D E) (e : E) :
    dgFunctorHom A D E F G ⟶ dgFunctorHom A D (Complex A)
      ((functorGraph A D E F).leftAt e) ((functorGraph A D E G).leftAt e) :=
  dgFunctorHomPost A D E (RightModule A E) (dgYoneda A E) F G ≫
    dgFunctorHomPost A D (RightModule A E) (Complex A) (moduleEvaluationDG A E e)
      (functorGraph A D E F).toFunctor (functorGraph A D E G).toFunctor

/-- 関手 Hom の二回の後合成は、元の同じ閉単位を保存する。 -/
lemma dgFunctorGraphLeftEnd_identity (F : DGFunctor A D E) (e : E) :
    dgFunctorIdentity A D E F ≫ dgFunctorGraphLeftEnd A D E F F e =
      dgFunctorIdentity A D (Complex A) ((functorGraph A D E F).leftAt e) := by
  unfold dgFunctorGraphLeftEnd
  dsimp only [functorGraph, Bimodule.toFunctor, Bimodule.leftAt]
  rw [← Category.assoc, dgFunctorHomPost_identity, dgFunctorHomPost_identity]

/-- 関手 Hom の二回の後合成は、元の同じ全次数合成を保存する。 -/
lemma dgFunctorGraphLeftEnd_composition (F G H : DGFunctor A D E) (e : E) :
    dgFunctorComposition A D E F G H ≫ dgFunctorGraphLeftEnd A D E F H e =
      (dgFunctorGraphLeftEnd A D E F G e ⊗ₘ dgFunctorGraphLeftEnd A D E G H e) ≫
        dgFunctorComposition A D (Complex A) ((functorGraph A D E F).leftAt e)
          ((functorGraph A D E G).leftAt e) ((functorGraph A D E H).leftAt e) := by
  unfold dgFunctorGraphLeftEnd
  dsimp only [functorGraph, Bimodule.toFunctor, Bimodule.leftAt]
  rw [← Category.assoc, dgFunctorHomPost_composition, Category.assoc,
    dgFunctorHomPost_composition, tensorHom_comp_tensorHom_assoc]

/-- 元の入力 Hom 複体から、実 graph の左加群の既存 Hom への chain map。 -/
def dgFunctorGraphLeftHom (F G : DGFunctor A D E) (e : E) :
    dgFunctorHom A D E F G ⟶
      leftModuleHom A D ((functorGraph A D E F).leftAt e) ((functorGraph A D E G).leftAt e) :=
  dgFunctorGraphLeftEnd A D E F G e ≫ dgLeftModuleHomComparison A D
    ((functorGraph A D E F).leftAt e) ((functorGraph A D E G).leftAt e)

/-- 元の各対象での Hom 評価は、元の入力・Yoneda・加群の評価の合成。 -/
lemma dgFunctorGraphLeftHom_π (F G : DGFunctor A D E) (e : E) (d : D) :
    dgFunctorGraphLeftHom A D E F G e ≫ leftModuleHomπ A D
        ((functorGraph A D E F).leftAt e) ((functorGraph A D E G).leftAt e) d =
      dgFunctorHomπ A D E F G d ≫ yonedaHom A E (F.obj d) (G.obj d) ≫
        moduleHomπ A E (representable A (F.obj d)) (representable A (G.obj d)) e := by
  rw [dgFunctorGraphLeftHom, Category.assoc, dgLeftModuleHomComparison_π]
  unfold dgFunctorGraphLeftEnd
  dsimp only [functorGraph, Bimodule.toFunctor, Bimodule.leftAt]
  rw [Category.assoc, dgFunctorHomPost_π]
  have h := congrArg (fun k => k ≫ (moduleEvaluationDG A E e).map
    ((F.comp (dgYoneda A E)).obj d) ((G.comp (dgYoneda A E)).obj d))
      (dgFunctorHomPost_π A D E (RightModule A E) (dgYoneda A E) F G d)
  simpa only [Category.assoc, DGFunctor.comp, EnrichedFunctor.comp, dgYoneda, DGFunctor.ofHomMaps,
    moduleEvaluationDG] using h

/-- 元の入力 Hom の単位は、同じ実 graph 左加群 Hom の単位へ送られる。 -/
lemma dgFunctorGraphLeftHom_identity (F : DGFunctor A D E) (e : E) :
    dgFunctorIdentity A D E F ≫ dgFunctorGraphLeftHom A D E F F e =
      moduleIdentity A Dᵒᵖ ((functorGraph A D E F).leftAt e).toRightOpposite := by
  have h := congrArg (fun k => k ≫ dgLeftModuleHomComparison A D
    ((functorGraph A D E F).leftAt e) ((functorGraph A D E F).leftAt e))
      (dgFunctorGraphLeftEnd_identity A D E F e)
  simpa only [dgFunctorGraphLeftHom, Category.assoc] using h.trans
    (dgLeftModuleHomComparison_identity A D ((functorGraph A D E F).leftAt e))

/-- 元の入力 Hom の合成は、同じ実 graph 左加群 Hom の合成へ送られる。 -/
lemma dgFunctorGraphLeftHom_composition (F G H : DGFunctor A D E) (e : E) :
    dgFunctorComposition A D E F G H ≫ dgFunctorGraphLeftHom A D E F H e =
      (dgFunctorGraphLeftHom A D E F G e ⊗ₘ dgFunctorGraphLeftHom A D E G H e) ≫
        moduleComposition A Dᵒᵖ ((functorGraph A D E F).leftAt e).toRightOpposite
          ((functorGraph A D E G).leftAt e).toRightOpposite
          ((functorGraph A D E H).leftAt e).toRightOpposite := by
  have h := congrArg (fun k => k ≫ dgLeftModuleHomComparison A D
    ((functorGraph A D E F).leftAt e) ((functorGraph A D E H).leftAt e))
      (dgFunctorGraphLeftEnd_composition A D E F G H e)
  have hc := congrArg (fun k =>
    (dgFunctorGraphLeftEnd A D E F G e ⊗ₘ
      dgFunctorGraphLeftEnd A D E G H e) ≫ k)
    (dgLeftModuleHomComparison_composition A D ((functorGraph A D E F).leftAt e)
      ((functorGraph A D E G).leftAt e) ((functorGraph A D E H).leftAt e))
  simp only [Category.assoc] at h hc
  simpa only [dgFunctorGraphLeftHom, Category.assoc, tensorHom_comp_tensorHom_assoc]
    using h.trans hc

end SerrePositivity.KST.SConstruction
