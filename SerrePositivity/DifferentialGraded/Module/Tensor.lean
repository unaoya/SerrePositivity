module
public import SerrePositivity.DifferentialGraded.Complexes.TensorEnriched
public import SerrePositivity.DifferentialGraded.Module.Action

/-! # 右 dg 加群の左 tensor と自由加群の対象

作用は左 tensor の豊穣関手との合成で構成する。
通常の閉零関手への置換をせず、全次数の作用・単位・合成を保持する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex Opposite
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 右加群 M の値に非有界複体 K を左 tensor する。 -/
abbrev tensorModule (K : Complex A) (M : RightModule A D) : RightModule A D :=
  RightModule.ofFunctor (DGFunctor.comp M.toFunctor (tensorLeftDG K))

/-- tensor 加群の斉次右作用。射の次数 p が K の次数 i を越える符号。 -/
lemma tensorModule_action (K : Complex A) (M : RightModule A D) (x y : Dᵒᵖ)
    (p i j a b n : ℤ) (ha : i + j = a) (hb : j + p = b) (hn : a + p = n)
    (f : GradedHom A x y p) (t : K.X i) (v : (M.obj x).X j) :
    moduleAction A (tensorModule K M) f
      (ιTensorObj K (M.obj x) i j a ha (t ⊗ₜ[A] v)) hn =
    (p * i).negOnePow • ιTensorObj K (M.obj y) i b n (by omega)
      (t ⊗ₜ[A] moduleAction A M f v hb) := by
  change ((tensorLeftHom K (M.obj x) (M.obj y)).f p ((M.map x y).f p f)).v a n hn
    (ιTensorObj K (M.obj x) i j a ha (t ⊗ₜ[A] v)) = _
  exact tensorLeftHom_apply_of_sum K (M.obj x) (M.obj y) p i j a b n ha hb hn _ t v

/-- x において複体 K で生成される自由右加群の対象。 -/
abbrev freeModule (x : D) (K : Complex A) : RightModule A D :=
  tensorModule K (representable A x)

/-- 自由加群の値は K⊗Hom_D(y,x)。 -/
lemma freeModule_obj (x y : D) (K : Complex A) :
    (freeModule x K).obj (op y) = K ⊗ (y ⟶[Complex A] x) := rfl
end SerrePositivity.DifferentialGraded
