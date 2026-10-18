module

public import SerrePositivity.KST.DerivedBlowup.DiagramModuleUnitCoherence
public import SerrePositivity.DifferentialGraded.Complexes.UnitorCochainNaturality

/-!
概要：KST §3.1 の指定包含単位矢による局所自己 Hom の作用。
方針：包含上の合成公式から局所 dg 代数の左単位則へ戻す。
規約：任意の包含 i≤j について Hom(i,j) を目標代数へ同定する。
使われ方：共変 representable の局所 regular 加群との比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory CategoryTheory.MonoidalCategory
open DifferentialGraded

variable {R : Type u} [CommRing R] {J : Type v} [Preorder J] [DecidableLE J]
variable (F : J ⥤ Mon (Complex R))

/-- 概要：包含の指定単位矢への前合成は局所代数から当該 Hom への標準同定。
方針：二つの Hom の包含と合成公式を使い、目標代数の左単位律を適用する。
規約：KST §3.1。使われ方：局所 regular 加群比較の成分の可逆性。 -/
theorem diagramModuleTransitionUnit_action {i j : J} (h : i ≤ j) :
    (λ_ (F.obj j).X).inv ≫
      (diagramModuleTransitionUnit F h ⊗ₘ diagramModuleHomInclusion F (le_refl j)) ≫
        diagramModuleComp F i j j = diagramModuleHomInclusion F h := by
  have ht : diagramModuleTransitionUnit F h ⊗ₘ diagramModuleHomInclusion F (le_refl j) =
      (MonObj.one (X := (F.obj j).X) ⊗ₘ 𝟙 (F.obj j).X) ≫
        (diagramModuleHomInclusion F h ⊗ₘ diagramModuleHomInclusion F (le_refl j)) := by
    rw [tensorHom_comp_tensorHom, Category.id_comp]
    rfl
  rw [ht, Category.assoc, diagramModuleComp_on_le]
  rw [show F.map (homOfLE (le_refl j)) = 𝟙 (F.obj j) from F.map_id j]
  simp only [Mon.id_hom', id_tensorHom_id, Category.id_comp]
  rw [tensorHom_id, MonObj.one_mul_assoc, Iso.inv_hom_id_assoc]

/-- 概要：指定包含単位の局所斉次射への作用は Hom の標準同定に一致する。
方針：複体上の単位作用公式を各次数で評価し、逆単位子の純 tensor 表示を使う。
規約：KST §3.1。使われ方：閉零 Yoneda 比較の各次数での計算。 -/
theorem diagramModuleTransitionUnit_forward {i j : J} (h : i ≤ j) (q : ℤ)
    (z : (F.obj j).X.X q) :
    forward R (D := DiagramModuleCoefficientObject F) (x := ⟨i⟩) (y := ⟨j⟩) (z := ⟨j⟩)
      (cycleFromUnit (diagramModuleHom F i j) (diagramModuleTransitionUnit F h)).val
      ((diagramModuleHomInclusion F (le_refl j)).f q z) (zero_add q) =
        (diagramModuleHomInclusion F h).f q z := by
  have he := congrArg (fun f : (F.obj j).X ⟶ diagramModuleHom F i j => f.f q z)
    (diagramModuleTransitionUnit_action F h)
  simp only [chain_comp_apply] at he
  rw [complexLeftUnitor_inv_apply, tensorMap_apply] at he
  exact he

/-- 概要：二つの指定包含単位の cycle の合成は直接包含の単位の cycle。
方針：閉零単位矢の三重整合性を単位複体の標準生成元で評価する。
規約：KST §3.1。使われ方：構造加群の単位生成元と指定遷移の整合性。 -/
theorem diagramModuleTransitionUnit_forward_comp {i j k : J} (h : i ≤ j) (g : j ≤ k) :
    forward R (D := DiagramModuleCoefficientObject F) (x := ⟨i⟩) (y := ⟨j⟩) (z := ⟨k⟩)
      (cycleFromUnit (diagramModuleHom F i j) (diagramModuleTransitionUnit F h)).val
      (cycleFromUnit (diagramModuleHom F j k) (diagramModuleTransitionUnit F g)).val rfl =
      (cycleFromUnit (diagramModuleHom F i k) (diagramModuleTransitionUnit F (h.trans g))).val := by
  have he := congrArg (fun f : 𝟙_ (Complex R) ⟶ diagramModuleHom F i k => (cycleFromUnit _ f).val)
    (diagramModuleTransitionUnit_comp F h g)
  rw [cycleFromUnit_postcomp] at he
  change (diagramModuleComp F i j k).f 0
    ((((λ_ (𝟙_ (Complex R))).inv ≫
      (diagramModuleTransitionUnit F h ⊗ₘ diagramModuleTransitionUnit F g)).f 0) (1 : R)) = _ at he
  rw [unit_tensor_apply] at he
  exact he

end SerrePositivity.KST.DerivedBlowup
