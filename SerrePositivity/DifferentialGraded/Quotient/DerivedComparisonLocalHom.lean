module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonGradedTensor
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonFiltrationZero
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonFiltrationColimit
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonColimitQuasiIso
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.CategoryTheory.Filtered.Connected

/-! # 片側 K-flat 条件と S に直交する対象上の Hom 比較

この段階では実際の dg 圏の対象 x,y を扱う。
Verdier 分母を添字とするホモトピー圏内の図式との比較は別工程である。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits HomologicalComplex
variable (A : Type u) [CommRing A]

lemma shortExact_quasiIso_f_of_acyclic (S : ShortComplex (Complex A)) (hS : S.ShortExact)
    (h₃ : S.X₃.Acyclic) : QuasiIso S.f := by
  constructor
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hm : Mono (homologyMap S.f i) :=
    (hS.homology_exact₁ (i - 1) i (by change i - 1 + 1 = i; omega)).mono_g_iff.mpr
      ((h₃ (i - 1)).isZero_homology.eq_zero_of_src _)
  have he : Epi (homologyMap S.f i) :=
    (hS.homology_exact₂ i).epi_f_iff.mpr ((h₃ i).isZero_homology.eq_zero_of_tgt _)
  exact isIso_of_mono_of_epi _

variable (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 空 path の包含を各長さ段階に因子化する。 -/
def originalToLength (S : Set D) (x y : D) (n : ℕ) :
    homObject A D x y ⟶ lengthComplex A D S x y n :=
  lengthZeroMap A D S x y ≫ lengthMap A D S x y (Nat.zero_le n)

@[reassoc] lemma originalToLength_inclusion (S : Set D) (x y : D) (n : ℕ) :
    originalToLength A D S x y n ≫ lengthInclusion A D S x y n =
      originalHomInclusion A D S x y := by
  rw [originalToLength, Category.assoc, lengthMap_inclusion, lengthZeroMap_inclusion]

lemma originalToLength_quasiIso (S : Set D) (x y : D)
    (h : ∀ n, (fixedLengthHom A D S x y (n + 1)).Acyclic) (n : ℕ) :
    QuasiIso (originalToLength A D S x y n) := by
  induction n with
  | zero =>
    rw [originalToLength, lengthMap_refl, Category.comp_id]
    infer_instance
  | succ n ih =>
    have : QuasiIso (lengthMap A D S x y (Nat.le_succ n)) :=
      shortExact_quasiIso_f_of_acyclic A (lengthLayerShortComplex A D S x y n)
        (lengthLayer_shortExact A D S x y n) (h n)
    have hc : originalToLength A D S x y (n + 1) =
        originalToLength A D S x y n ≫ lengthMap A D S x y (Nat.le_succ n) := by
      rw [originalToLength, originalToLength, Category.assoc, lengthMap_comp]
    rw [hc]
    infer_instance

def originalLengthTransformation (S : Set D) (x y : D) :
    (Functor.const ℕ).obj (homObject A D x y) ⟶ lengthDiagram A D S x y where
  app n := originalToLength A D S x y n
  naturality {m n} f := by
    change 𝟙 _ ≫ originalToLength A D S x y n =
      originalToLength A D S x y m ≫ lengthMap A D S x y (leOfHom f)
    rw [Category.id_comp, originalToLength, originalToLength, Category.assoc, lengthMap_comp]

/-- 正の全層が acyclic なら、元の Hom の包含は最終 Hom への擬同型。 -/
lemma originalHomInclusion_quasiIso_of_layers (S : Set D) (x y : D)
    (h : ∀ n, (fixedLengthHom A D S x y (n + 1)).Acyclic) :
    QuasiIso (originalHomInclusion A D S x y) := by
  have : AB5OfSize.{0, 0} (ModuleCat.{u} A) := AB5OfSize_of_univLE (ModuleCat.{u} A)
  have : IsConnected ℕ := IsFiltered.isConnected _
  let α := originalLengthTransformation A D S x y
  have : QuasiIso (colimMap α) :=
    complex_colimMap_quasiIso A α (originalToLength_quasiIso A D S x y h)
  let e := (isColimitConstCocone ℕ (homObject A D x y)).coconePointUniqueUpToIso
    (colimit.isColimit ((Functor.const ℕ).obj (homObject A D x y)))
  have he : e.hom = colimit.ι ((Functor.const ℕ).obj (homObject A D x y)) 0 := by
    have h₀ :=
      (isColimitConstCocone ℕ (homObject A D x y)).comp_coconePointUniqueUpToIso_hom
        (colimit.isColimit _) (0 : ℕ)
    change 𝟙 (homObject A D x y) ≫ e.hom =
      colimit.ι ((Functor.const ℕ).obj (homObject A D x y)) 0 at h₀
    simpa only [Category.id_comp] using h₀
  have hc : e.hom ≫ colimMap α ≫ (lengthColimitIso A D S x y).hom =
      originalHomInclusion A D S x y := by
    rw [he, ← Category.assoc, ι_colimMap, Category.assoc, lengthColimitIso_ι]
    exact originalToLength_inclusion A D S x y 0
  rw [← hc]
  infer_instance

/-- Hom(−,S) が K-flat で y が S に右直交するときの、明示的商 Hom との比較。 -/
lemma originalHomInclusion_quasiIso_into (S : Set D) (h : homIntoKFlat A D S) (x y : D)
    (hy : ∀ b : S, (homObject A D b.val y).Acyclic) :
    QuasiIso (originalHomInclusion A D S x y) :=
  originalHomInclusion_quasiIso_of_layers A D S x y
    (fixedLengthHom_acyclic_into A D S h x y hy)

/-- Hom(S,−) が K-flat で x が S に左直交するときの、明示的商 Hom との比較。 -/
lemma originalHomInclusion_quasiIso_outOf (S : Set D) (h : homOutOfKFlat A D S) (x y : D)
    (hx : ∀ b : S, (homObject A D x b.val).Acyclic) :
    QuasiIso (originalHomInclusion A D S x y) :=
  originalHomInclusion_quasiIso_of_layers A D S x y
    (fixedLengthHom_acyclic_outOf A D S h x y hx)

end SerrePositivity.DifferentialGraded.DGQuotient
