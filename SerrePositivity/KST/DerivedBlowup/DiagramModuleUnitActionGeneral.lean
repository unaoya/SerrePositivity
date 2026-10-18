module

public import SerrePositivity.KST.DerivedBlowup.DiagramModuleUnitAction

/-!
概要：KST §3.1 の指定包含単位は任意の後続 Hom への左作用で単位となる。
方針：包含上の合成公式と係数遷移の単位保存を使う。
規約：二つの包含の合成先の Hom 同定を明示する。
使われ方：O(m) の局所生成元に対する指定遷移の計算。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory CategoryTheory.MonoidalCategory DifferentialGraded

variable {R : Type u} [CommRing R] {J : Type v} [Preorder J] [DecidableLE J]
variable (F : J ⥤ Mon (Complex R))

/-- 概要：包含単位の任意の後続 Hom への作用は直接包含の標準同定。
方針：単位射を tensor から取り出し、合成公式と係数遷移後の左単位律を使う。
規約：KST §3.1。使われ方：構造生成元への重み付け遷移の計算。 -/
theorem diagramModuleTransitionUnit_action_general {i j k : J} (h : i ≤ j) (g : j ≤ k) :
    (λ_ (F.obj k).X).inv ≫
      (diagramModuleTransitionUnit F h ⊗ₘ diagramModuleHomInclusion F g) ≫
        diagramModuleComp F i j k = diagramModuleHomInclusion F (h.trans g) := by
  have ht : diagramModuleTransitionUnit F h ⊗ₘ diagramModuleHomInclusion F g =
      (MonObj.one (X := (F.obj j).X) ⊗ₘ 𝟙 (F.obj k).X) ≫
        (diagramModuleHomInclusion F h ⊗ₘ diagramModuleHomInclusion F g) := by
    rw [tensorHom_comp_tensorHom, Category.id_comp]
    rfl
  rw [ht, Category.assoc, diagramModuleComp_on_le]
  change (λ_ (F.obj k).X).inv ≫
    (MonObj.one (X := (F.obj j).X) ▷ (F.obj k).X) ≫
      diagramAlgebraMul (F.map (homOfLE g)) ≫
        diagramModuleHomInclusion F (h.trans g) = _
  rw [diagramAlgebraMul_one_assoc, Iso.inv_hom_id_assoc]

/-- 概要：包含単位と任意の後続 Hom の斉次元の積は直接 Hom 同定に一致する。
方針：複体の作用公式を純 tensor で評価する。
規約：KST §3.1。使われ方：捻り加群の局所生成元の遷移を計算する。 -/
theorem diagramModuleTransitionUnit_forward_general {i j k : J} (h : i ≤ j) (g : j ≤ k)
    (q : ℤ) (z : (F.obj k).X.X q) :
    forward R (D := DiagramModuleCoefficientObject F) (x := ⟨i⟩) (y := ⟨j⟩) (z := ⟨k⟩)
      (cycleFromUnit (diagramModuleHom F i j) (diagramModuleTransitionUnit F h)).val
      ((diagramModuleHomInclusion F g).f q z) (zero_add q) =
        (diagramModuleHomInclusion F (h.trans g)).f q z := by
  have he := congrArg (fun f : (F.obj k).X ⟶ diagramModuleHom F i k => f.f q z)
    (diagramModuleTransitionUnit_action_general F h g)
  simp only [chain_comp_apply] at he
  rw [complexLeftUnitor_inv_apply, tensorMap_apply] at he
  exact he

end SerrePositivity.KST.DerivedBlowup
