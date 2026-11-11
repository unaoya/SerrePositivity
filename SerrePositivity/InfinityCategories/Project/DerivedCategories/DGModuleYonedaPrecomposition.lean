module
public import SerrePositivity.DifferentialGraded.Module.Graded
public import SerrePositivity.DifferentialGraded.Module.Hom.ConeComparison

/-! # 全 Hom Yoneda の逆写像と元の次数零元の前合成

概要：Yoneda 逆写像の全斉次成分を評価し、次数零元による前合成を加群作用へ戻す。
方針：Yoneda 拡張と単位での評価の公式を、Hom end の通常順合成へ適用する。
規約：全整数次数を保持する。使われ方：商の斉次分数表示の比較式を元の Hom へ戻す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded HomologicalComplex CochainComplex HomComplex Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 全 Hom Yoneda の逆写像の各対象成分は Yoneda 拡張。 -/
lemma dgYonedaInverse_π (x q : D) (N : RightModule A D) :
    (dgYonedaIso A x N).inv ≫ moduleHomπ A D (representable A x) N q =
      yonedaExtensionApp A x N (𝟙 _) (op q) :=
  moduleHomEquiv_symm_π A D _ _ _ (yonedaExtension A x N (𝟙 _)) q

/-- Yoneda 逆写像の斉次成分の作用公式。 -/
lemma dgYonedaInverse_element (x q : D) (N : RightModule A D) (n r t : ℤ)
    (ht : r + n = t) (c : (N.obj (op x)).X n) (s : GradedHom A q x r) :
    (((moduleHomπ A D (representable A x) N q).f n ((dgYonedaIso A x N).inv.f n c)).v r t ht)
      s = (n * r).negOnePow • moduleAction A N s c (by omega) := by
  have hp := congrArg (fun f => f.f n c) (dgYonedaInverse_π A D x q N)
  change (moduleHomπ A D (representable A x) N q).f n ((dgYonedaIso A x N).inv.f n c) = _ at hp
  rw [hp]
  simpa only [HomologicalComplex.id_f, ModuleCat.id_apply] using
    yonedaExtensionApp_apply A x N (𝟙 _) (op q) n r t ht c s

/-- 原の次数零元の Yoneda 像で前合成して評価すると、元の加群作用になる。 -/
lemma dgYonedaInverse_precompose_evaluation (x q : D) (N : RightModule A D) (n : ℤ)
    (c : (N.obj (op x)).X n) (s : GradedHom A q x 0) :
    (dgYonedaIso A q N).hom.f n
      (compose A (D := RightModule A D) ((dgYonedaIso A x N).inv.f n c)
        ((yonedaHom A D q x).f 0 s) (zero_add n)) =
      moduleAction A N s c (add_zero n) := by
  change (yonedaEvaluateFamily A q N
    (fun z => moduleHomπ A D (representable A q) N z.unop)).f n _ = _
  rw [yonedaEvaluateFamily_apply, moduleHomCompose_π,
    Cochain.comp_v _ _ _ 0 0 n (by decide) (zero_add n), ModuleCat.comp_apply,
    yonedaHom_element]
  simp only [Int.mul_zero, Int.negOnePow_zero, one_smul, forward_unit]
  rw [dgYonedaInverse_element]
  simp only [Int.mul_zero, Int.negOnePow_zero, one_smul]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
