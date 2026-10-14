module
public import SerrePositivity.DifferentialGraded.Complexes.Closed
public import SerrePositivity.DifferentialGraded.Category.Components
public import SerrePositivity.DifferentialGraded.Category.Examples
public import SerrePositivity.DifferentialGraded.Functor.Basic
public import Mathlib.CategoryTheory.Enriched.Opposite

/-! # 右 dg 加群

対象は Dᵒᵖ から Ch(A) への豊穣関手であり、通常の関手圏に置き換えない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 右 dg 加群の対象は既存の豊穣関手。
型別名は全次数自然性を持つ射の圏構造を選ぶためのもので、対象データを複製しない。 -/
def RightModule := DGFunctor A Dᵒᵖ (Complex A)

/-- 左 dg 加群の対象。 -/
abbrev LeftModule := DGFunctor A D (Complex A)

namespace RightModule
variable {A D}

/-- 右加群の対象データを既存の豊穣関手として読む。 -/
abbrev toFunctor (M : RightModule A D) : DGFunctor A Dᵒᵖ (Complex A) := M

/-- 豊穣関手を右加群の対象として読む。 -/
abbrev ofFunctor (F : DGFunctor A Dᵒᵖ (Complex A)) : RightModule A D := F

/-- 右加群の対象での値。 -/
abbrev obj (M : RightModule A D) (x : Dᵒᵖ) : Complex A := M.toFunctor.obj x

/-- 右加群の全次数 Hom 射。 -/
abbrev map (M : RightModule A D) (x y : Dᵒᵖ) :
    (x ⟶[Complex A] y) ⟶ homComplex A (M.obj x) (M.obj y) := M.toFunctor.map x y
end RightModule

/-- 対象データの型別名の往復は定義上の恒等写像。 -/
lemma rightModule_roundtrip (M : RightModule A D) :
    RightModule.ofFunctor M.toFunctor = M := rfl

/-- 右加群の対象 x での値。射の評価関手は全次数自然性の圏構造の後に構成する。 -/
abbrev moduleValue (x : D) (M : RightModule A D) : Complex A := M.obj (op x)

/-- 豊穣 opposite の Hom は順を逆にした元の Hom 複体。 -/
lemma opposite_hom (x y : Dᵒᵖ) :
    EnrichedCategory.Hom (V := Complex A) x y =
      EnrichedCategory.Hom (V := Complex A) y.unop x.unop := rfl

/-- 豊穣 opposite の合成には Koszul braiding が入る。 -/
lemma opposite_composition (x y z : Dᵒᵖ) :
    eComp (Complex A) x y z =
      (signedSwap (y.unop ⟶[Complex A] x.unop) (z.unop ⟶[Complex A] y.unop)).hom ≫
        eComp (Complex A) z.unop y.unop x.unop := rfl

/-- 豊穣順の opposite 合成の斉次公式。 -/
lemma opposite_forward (x y z : Dᵒᵖ) (p q n : ℤ) (hn : p + q = n)
    (f : GradedHom A x y p) (g : GradedHom A y z q) :
    forward A f g hn = (p * q).negOnePow •
      forward A (x := z.unop) (y := y.unop) (z := x.unop) g f (by omega) := by
  unfold forward
  rw [opposite_composition A D x y z]
  change (eComp (Complex A) z.unop y.unop x.unop).f n
    ((signedSwap (y.unop ⟶[Complex A] x.unop) (z.unop ⟶[Complex A] y.unop)).hom.f n
      (ιTensorObj (y.unop ⟶[Complex A] x.unop) (z.unop ⟶[Complex A] y.unop)
        p q n hn (f ⊗ₜ[A] g))) = _
  rw [signedSwap_apply]
  simp only [Units.smul_def, map_zsmul]

/-- 通常順の opposite 合成は元の逆順合成に (-1)^(pq) を掛ける。 -/
lemma opposite_compose (x y z : Dᵒᵖ) (p q n : ℤ) (hn : p + q = n)
    (f : GradedHom A x y p) (g : GradedHom A y z q) :
    compose A g f hn = (p * q).negOnePow •
      compose A (x := z.unop) (y := y.unop) (z := x.unop) f g (by omega) := by
  unfold compose forward
  rw [opposite_composition]
  change (p * q).negOnePow •
    (eComp (Complex A) z.unop y.unop x.unop).f n
      ((signedSwap (y.unop ⟶[Complex A] x.unop)
        (z.unop ⟶[Complex A] y.unop)).hom.f n
          (ιTensorObj (y.unop ⟶[Complex A] x.unop) (z.unop ⟶[Complex A] y.unop)
            p q n hn (f ⊗ₜ[A] g))) = _
  rw [signedSwap_apply]
  simp only [Units.smul_def, map_zsmul, smul_smul, mul_comm p q]
end SerrePositivity.DifferentialGraded
