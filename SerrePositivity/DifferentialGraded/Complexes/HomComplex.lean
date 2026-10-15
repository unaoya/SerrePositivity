module
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import SerrePositivity.HomologicalAlgebra.CochainTensor

/-! # 非有界 A 複体と A 線形 Hom 複体

微分は +1、ホモトピーは −1。環・加群は同じ宇宙 u に置く。
対象の有界性・有限性・環の標数には仮定を置かない。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CochainComplex HomComplex
variable (A : Type u) [CommRing A]

/-- 任意の可換環上の整数コチェイン複体。非有界対象を含む。 -/
abbrev Complex := CochainComplex (ModuleCat.{u} A) ℤ

/-- Mathlib の A 線形 Hom 複体を主データとして再利用する。 -/
abbrev homComplex (X Y : Complex A) : Complex A := CochainComplex.linearHomComplex A X Y

variable {A} {X Y Z : Complex A}

/-- 次数 n の線形射の族。Mathlib の Triplet により次数の等式を保持する。 -/
abbrev Homogeneous (X Y : Complex A) (n : ℤ) := Cochain X Y n

/-- Hom 微分の二乗は零。非隣接次数でも成立する。 -/
lemma differential_squared (p q r : ℤ) (f : Homogeneous X Y p) :
    δ q r (δ p q f) = 0 := δ_δ p q r f

/-- 通常順 μ(g,f)=g∘f の Leibniz 則。符号は後に作用する g の次数 q。 -/
lemma differential_comp {p q n : ℤ} (f : Homogeneous X Y p) (g : Homogeneous Y Z q)
    (h : p + q = n) :
    δ n (n + 1) (f.comp g h) =
      f.comp (δ q (q + 1) g) (by omega) +
      q.negOnePow • (δ p (p + 1) f).comp g (by omega) :=
  δ_comp f g h (p + 1) (q + 1) (n + 1) rfl rfl rfl

/-- 閉次数零の射と chain map の A 線形同値。 -/
def closedZeroEquiv (X Y : Complex A) : (X ⟶ Y) ≃ₗ[A] Cocycle X Y 0 :=
  { Cocycle.equivHom X Y with map_smul' := Cocycle.ofHom_smul }

/-- contracting homotopy は次数 −1、その境界が恒等射なら対象を収縮する。 -/
def contractingHomotopy (X : Complex A)
    (h : Homogeneous X X (-1)) (dh : δ (-1) 0 h = Cochain.ofHom (𝟙 X)) :
    Homotopy (𝟙 X) 0 :=
  (Cochain.equivHomotopy (𝟙 X) 0).symm ⟨h, by simp [dh]⟩
end SerrePositivity.DifferentialGraded
