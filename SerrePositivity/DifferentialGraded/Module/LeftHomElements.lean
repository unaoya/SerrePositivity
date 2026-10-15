module
public import SerrePositivity.DifferentialGraded.Module.LeftCategory
public import SerrePositivity.DifferentialGraded.Module.LeftAction
public import SerrePositivity.DifferentialGraded.Module.HomElements

/-! # 左加群の主Hom endの全次数自然性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

abbrev leftModuleHomπ (M N : LeftModule A D) (x : D) :
    leftModuleHom A D M N ⟶ homComplex A (M.obj x) (N.obj x) :=
  moduleHomπ A Dᵒᵖ M.toRightOpposite N.toRightOpposite (op x)

/-- 任意次数qの左加群Homと次数pの作用を交換する符号。 -/
lemma leftModuleHomElement_naturality {M N : LeftModule A D} (q : ℤ)
    (t : (leftModuleHom A D M N).X q) (x y : D) (p : ℤ) (f : GradedHom A x y p) :
    ((M.map x y).f p f).comp ((leftModuleHomπ A D M N y).f q t)
      (by omega : p + q = q + p) =
    (q * p).negOnePow • (((leftModuleHomπ A D M N x).f q t).comp
      ((N.map x y).f p f) rfl) := by
  have h := moduleHomElement_naturality A Dᵒᵖ q t (op (op x)) (op (op y)) p f
  change (((𝟙 _ ≫ M.map x y).f p f).comp ((leftModuleHomπ A D M N y).f q t)
      (by omega : p + q = q + p)) =
    (q * p).negOnePow • (((leftModuleHomπ A D M N x).f q t).comp
      ((𝟙 _ ≫ N.map x y).f p f) rfl) at h
  simpa only [Category.id_comp] using h

/-- 上のcochain自然性を任意の中間次数で評価する。 -/
lemma leftModuleHomElement_action {M N : LeftModule A D} {q p r s k n : ℤ}
    (t : (leftModuleHom A D M N).X q) (x y : D) (f : GradedHom A x y p)
    (m : (M.obj x).X r) (hs : r + p = s) (hk : r + q = k) (hn : s + q = n) :
    (((leftModuleHomπ A D M N y).f q t).v s n hn) (leftAction A M f m hs) =
    (q * p).negOnePow • leftAction A N f
      ((((leftModuleHomπ A D M N x).f q t).v r k hk) m) (by omega) := by
  have h := Cochain.congr_v (leftModuleHomElement_naturality A D q t x y p f)
    r n (by omega)
  rw [Cochain.comp_v _ _ _ r s n hs hn, Cochain.units_smul_v,
    Cochain.comp_v _ _ _ r k n hk (by omega)] at h
  exact congrArg (fun l => l m) h

end SerrePositivity.DifferentialGraded
