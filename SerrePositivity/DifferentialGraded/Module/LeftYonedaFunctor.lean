module
public import SerrePositivity.DifferentialGraded.Module.YonedaFunctor
public import SerrePositivity.DifferentialGraded.Module.LeftRepresentable
public import SerrePositivity.DifferentialGraded.Module.LeftHomElements

/-! # 左representableの代表対象に関する全Hom写像 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]


/-- opposite上のYoneda拡張を二重opposite表示の全自然族へ移す。 -/
def leftYonedaParam (z z' : D) :
    ModuleParamTrans A Dᵒᵖ (op z ⟶[Complex A] op z')
      (leftRepresentable A z).toRightOpposite (leftRepresentable A z').toRightOpposite where
  app x := yonedaExtensionApp A (op z) (representable A (op z')) (𝟙 _) x
  naturality x y := by
    have h := yonedaExtensionApp_naturality A (op z) (representable A (op z')) (𝟙 _) x y
    change (β_ (op z ⟶[Complex A] op z') (x ⟶[Complex A] y)).hom ≫
        ((𝟙 _ ≫ 𝟙 _ ≫ representableMap A (op z) x y) ⊗ₘ
          yonedaExtensionApp A (op z) (representable A (op z')) (𝟙 _) y) ≫
            enrichedComposition _ _ _ =
      (yonedaExtensionApp A (op z) (representable A (op z')) (𝟙 _) x ⊗ₘ
        (𝟙 _ ≫ 𝟙 _ ≫ representableMap A (op z') x y)) ≫ enrichedComposition _ _ _
    simpa only [Category.id_comp] using h

/-- 反変に動く代表対象のHomを左加群の全Homへ送る。 -/
def leftYonedaHom (z z' : D) :
    (op z ⟶[Complex A] op z') ⟶ leftModuleHom A D (leftRepresentable A z)
      (leftRepresentable A z') :=
  (moduleHomEquiv A Dᵒᵖ _ _ _).symm (leftYonedaParam A D z z')

@[reassoc]
lemma leftYonedaHom_π (z z' x : D) :
    leftYonedaHom A D z z' ≫
      leftModuleHomπ A D (leftRepresentable A z) (leftRepresentable A z') x =
    yonedaExtensionApp A (op z) (representable A (op z')) (𝟙 _) (op (op x)) :=
  moduleHomEquiv_symm_π A Dᵒᵖ _ _ _ (leftYonedaParam A D z z') (op x)

lemma leftYonedaHom_element (z z' x : D) {p r n : ℤ}
    (f : GradedHom A (op z) (op z') p) (h : GradedHom A z x r) (hn : r + p = n) :
    (((leftModuleHomπ A D (leftRepresentable A z) (leftRepresentable A z') x).f p
      ((leftYonedaHom A D z z').f p f)).v r n hn) h =
    forward A (D := D) (x := z') (y := z) (z := x) f h (by omega) := by
  have hp := congrArg (fun t => t.f p f) (leftYonedaHom_π A D z z' x)
  change (leftModuleHomπ A D (leftRepresentable A z) (leftRepresentable A z') x).f p
    ((leftYonedaHom A D z z').f p f) = _ at hp
  rw [hp]
  have he := yonedaExtensionApp_apply A (op z) (representable A (op z')) (𝟙 _)
    (op (op x)) p r n hn f h
  simp only [HomologicalComplex.id_f, ModuleCat.id_apply] at he
  change (((yonedaExtensionApp A (op z) (representable A (op z')) (𝟙 _) (op (op x))).f p f).v
      r n hn) h =
    (p * r).negOnePow • forward A (D := Dᵒᵖ) (x := op x) (y := op z) (z := op z') h f hn at he
  rw [opposite_forward, mul_comm r p, smul_smul, Int.units_mul_self, one_smul] at he
  exact he

end SerrePositivity.DifferentialGraded
