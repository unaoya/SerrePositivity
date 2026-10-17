module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonFlatness
public import SerrePositivity.DifferentialGraded.Quotient.Paths
public import SerrePositivity.DifferentialGraded.Tensor.SphereFreeKFlat

/-! # 片側局所 K-flat 仮定と path の係数複体

内部微分だけを持つ path 項を扱う。最終微分の長さ filtration は別工程である。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 入る Hom が K-flat なら、殺す対象を終点とする全ての内部 path 項が K-flat。 -/
lemma term_kFlat_into {S : Set D} (h : homIntoKFlat A D S)
    (w : Word S) (x : D) (b : S) : complexKFlat A (term A D w x b.val) := by
  induction w generalizing x with
  | nil => exact h x b
  | cons c w ih =>
    exact complexKFlat_tensor A (h x c)
      (complexKFlat_tensor A (complexSphere_kFlat A (-1)) (ih c.val))

/-- 出る Hom が K-flat なら、殺す対象を始点とする全ての内部 path 項が K-flat。 -/
lemma term_kFlat_outOf {S : Set D} (h : homOutOfKFlat A D S)
    (w : Word S) (b : S) (y : D) : complexKFlat A (term A D w b.val y) := by
  induction w generalizing b with
  | nil => exact h b y
  | cons c w ih =>
    exact complexKFlat_tensor A (h b c.val)
      (complexKFlat_tensor A (complexSphere_kFlat A (-1)) (ih c))

/-- 最後の Hom(b,y) を除き、最後の ε は残した path の前方係数。 -/
def pathPrefixWeight {S : Set D} : Word S → D → S → Complex A
  | [], x, b => homObject A D x b.val ⊗ epsilonComplex A
  | c :: w, x, b => homObject A D x c.val ⊗ (epsilonComplex A ⊗ pathPrefixWeight w c.val b)

/-- 最初の Hom(x,b) を除き、最初の ε は残した path の後方係数。 -/
def pathSuffixWeight {S : Set D} (w : Word S) (b : S) (y : D) : Complex A :=
  epsilonComplex A ⊗ term A D w b.val y

/-- path 添字を保持し、最後の Hom だけを右 tensor 因子に分離する。 -/
def termSnocWeightIso {S : Set D} (w : Word S) (x : D) (b : S) (y : D) :
    term A D (w ++ [b]) x y ≅ pathPrefixWeight A D w x b ⊗ homObject A D b.val y := by
  induction w generalizing x with
  | nil => exact (α_ (homObject A D x b.val) (epsilonComplex A) (homObject A D b.val y)).symm
  | cons c w ih =>
    exact (Iso.refl (homObject A D x c.val) ⊗ᵢ
      (Iso.refl (epsilonComplex A) ⊗ᵢ ih c.val)) ≪≫
      (Iso.refl (homObject A D x c.val) ⊗ᵢ
        (α_ (epsilonComplex A) (pathPrefixWeight A D w c.val b) (homObject A D b.val y)).symm) ≪≫
      (α_ (homObject A D x c.val) (epsilonComplex A ⊗ pathPrefixWeight A D w c.val b)
        (homObject A D b.val y)).symm

lemma pathPrefixWeight_kFlat {S : Set D} (h : homIntoKFlat A D S)
    (w : Word S) (x : D) (b : S) : complexKFlat A (pathPrefixWeight A D w x b) := by
  induction w generalizing x with
  | nil => exact complexKFlat_tensor A (h x b) (complexSphere_kFlat A (-1))
  | cons c w ih =>
    exact complexKFlat_tensor A (h x c)
      (complexKFlat_tensor A (complexSphere_kFlat A (-1)) (ih c.val))

lemma pathSuffixWeight_kFlat {S : Set D} (h : homOutOfKFlat A D S)
    (w : Word S) (b : S) (y : D) : complexKFlat A (pathSuffixWeight A D w b y) :=
  complexKFlat_tensor A (complexSphere_kFlat A (-1)) (term_kFlat_outOf A D h w b y)

/-- 前方係数との tensor は、任意の非有界 acyclic 複体を acyclic に保つ。 -/
lemma pathPrefixWeight_tensor_acyclic {S : Set D} (h : homIntoKFlat A D S)
    (w : Word S) (x : D) (b : S) (K : Complex A) (hK : K.Acyclic) :
    (pathPrefixWeight A D w x b ⊗ K).Acyclic :=
  pathPrefixWeight_kFlat A D h w x b K hK

/-- 前方係数との tensor は、末尾の任意の擬同型を保つ。末尾の平坦性は要求しない。 -/
lemma pathPrefixWeight_tensor_quasiIso {S : Set D} (h : homIntoKFlat A D S)
    (w : Word S) (x : D) (b : S) {K L : Complex A} (f : K ⟶ L) [QuasiIso f] :
    QuasiIso (cochainTensorMap (𝟙 (pathPrefixWeight A D w x b)) f) :=
  complexKFlat_quasiIso_right A (pathPrefixWeight_kFlat A D h w x b) f

/-- 後方係数との tensor は、先頭の任意の擬同型を保つ。先頭の平坦性は要求しない。 -/
lemma pathSuffixWeight_tensor_quasiIso {S : Set D} (h : homOutOfKFlat A D S)
    (w : Word S) (b : S) (y : D) {K L : Complex A} (f : K ⟶ L) [QuasiIso f] :
    QuasiIso (cochainTensorMap f (𝟙 (pathSuffixWeight A D w b y))) :=
  complexKFlat_quasiIso_left A (pathSuffixWeight_kFlat A D h w b y) f

end SerrePositivity.DifferentialGraded.DGQuotient
