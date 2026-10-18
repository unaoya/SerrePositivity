module

public import SerrePositivity.KST.DerivedBlowup.ExteriorUnit
public import Mathlib.Algebra.Homology.Single

/-!
概要：KST Def3.1 の Koszul 外積模型の標準添加射の係数写像。
方針：外積生成元を零へ送り、次数0以外を消すことを同次部分で検証する。
規約：任意の可換係数代数。解消性や正則性は仮定しない。
使われ方：普遍チャートの積・単位を保つ標準添加射。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory

variable {R S M : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M]

/-- 概要：全外積代数から係数代数への標準添加準同型。
方針：全外積生成元を零に送る普遍射を使う。
規約：KST Def3.1。使われ方：次数付き標準添加射の共通計算先。 -/
def exteriorAugmentation : ExteriorAlgebra R M →ₐ[R] S :=
  ExteriorAlgebra.lift R ⟨(0 : M →ₗ[R] S), fun _ => by simp⟩

/-- 概要：標準添加射は正の外積次数を消す。
方針：部分加群の積の帰納法で左側の外積生成元を零へ送る。
規約：KST Def3.1。使われ方：非零 cochain 次数の添加射の消滅。 -/
theorem exteriorAugmentation_positive (n : ℕ) (z : ExteriorAlgebra R M)
    (hz : z ∈ ExteriorAlgebra.exteriorPower R (n + 1) M) :
    exteriorAugmentation (S := S) z = 0 := by
  change z ∈ (LinearMap.range (ExteriorAlgebra.ι R (M := M))) ^ (n + 1) at hz
  rw [pow_succ'] at hz
  refine Submodule.mul_induction_on hz ?_ ?_
  · intro x hx y _
    obtain ⟨m, rfl⟩ := hx
    simp [exteriorAugmentation]
  · intro x y hx hy
    rw [map_add, hx, hy, add_zero]

/-- 概要：Koszul cochain の各次数の係数への線形射。
方針：総外積への包含と標準添加準同型を合成する。
規約：KST Def3.1。使われ方：次数0の鎖写像と積保存の成分。 -/
def exteriorCochainAugmentationComponent (d : M →ₗ[R] R) (q : ℤ) :
    (exteriorKoszulCochain d).X q →ₗ[R] S :=
  (exteriorAugmentation (R := R) (M := M) (S := S)).toLinearMap.comp
    (exteriorCochainInclusion d q)

/-- 概要：係数への標準添加成分は次数0以外で零。
方針：正 cochain 次数では定義域が零、負次数では正外積次数の消滅を使う。
規約：KST Def3.1。使われ方：単一複体への射の成分公式。 -/
theorem exteriorCochainAugmentationComponent_ne_zero (d : M →ₗ[R] R)
    (q : ℤ) (hq : q ≠ 0) : exteriorCochainAugmentationComponent (S := S) d q = 0 := by
  apply LinearMap.ext
  intro z
  change exteriorAugmentation (S := S) (exteriorCochainInclusion d q z) = 0
  by_cases hp : 0 < q
  · have := ModuleCat.subsingleton_of_isZero (exteriorKoszulCochain_isZero_X_pos d q hp)
    have hz : z = 0 := Subsingleton.elim _ _
    simp [hz]
  · have hn : (-q).toNat = ((-q).toNat - 1) + 1 := by omega
    apply exteriorAugmentation_positive ((-q).toNat - 1)
    rw [← hn]
    exact exteriorCochainInclusion_mem d q z

/-- 概要：係数代数で微分の値が零なら添加の次数0成分は境界を消す。
方針：次数−1の外積は生成加群の像なので、収縮は d の値になる。
規約：KST Def3.1。使われ方：標準添加射の鎖写像条件。 -/
theorem exteriorCochainAugmentationComponent_d (d : M →ₗ[R] R)
    (hd : ∀ m, algebraMap R S (d m) = 0) :
    (exteriorKoszulCochain d).d (-1) 0 ≫
      ModuleCat.ofHom (exteriorCochainAugmentationComponent (S := S) d 0) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  have hz := exteriorCochainInclusion_mem d (-1) z
  change exteriorCochainInclusion d (-1) z ∈
    (LinearMap.range (ExteriorAlgebra.ι R (M := M))) ^ 1 at hz
  rw [pow_one] at hz
  obtain ⟨m, hm⟩ := hz
  change exteriorAugmentation (S := S)
    (exteriorCochainInclusion d 0 (((exteriorKoszulCochain d).d (-1) 0).hom z)) = 0
  rw [show (0 : ℤ) = -1 + 1 from rfl, exteriorCochainInclusion_d, ← hm,
    CliffordAlgebra.contractLeft_ι]
  exact (exteriorAugmentation (R := R) (M := M) (S := S)).commutes (d m) |>.trans (hd m)

/-- 概要：Koszul 外積複体から係数代数の次数0単一複体への標準添加射。
方針：明示的な次数0成分と境界消滅を mkHomToSingle に渡す。
規約：KST Def3.1、H⁰ 同型の選択に依存しない。
使われ方：普遍チャート cdga の標準添加射の underlying 鎖写像。 -/
def exteriorKoszulAugmentation (d : M →ₗ[R] R)
    (hd : ∀ m, algebraMap R S (d m) = 0) :
    exteriorKoszulCochain d ⟶
      (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj (ModuleCat.of R S) :=
  HomologicalComplex.mkHomToSingle
    (ModuleCat.ofHom (exteriorCochainAugmentationComponent d 0)) (fun i hi => by
      have hi' : i = -1 := by
        change i + 1 = 0 at hi
        omega
      subst i
      exact exteriorCochainAugmentationComponent_d d hd)

/-- 概要：標準添加の各次数成分は Koszul 積を保つ。
方針：総外積への包含の積公式と添加準同型の積保存を使う。
規約：KST Def3.1。使われ方：単一複体への添加射の乗法適合性。 -/
theorem exteriorCochainAugmentationComponent_mul (d : M →ₗ[R] R)
    (p q n : ℤ) (h : p + q = n)
    (x : (exteriorKoszulCochain d).X p) (y : (exteriorKoszulCochain d).X q) :
    exteriorCochainAugmentationComponent (S := S) d n (exteriorCochainBilinear d p q n h x y) =
      exteriorCochainAugmentationComponent (S := S) d p x *
        exteriorCochainAugmentationComponent (S := S) d q y := by
  change exteriorAugmentation (S := S)
      (exteriorCochainInclusion d n (exteriorCochainBilinear d p q n h x y)) = _
  rw [exteriorCochainInclusion_product, map_mul]
  rfl

/-- 概要：標準添加の次数0成分は単位を保つ。
方針：Koszul 単位元の総外積への像が1であることを使う。
規約：KST Def3.1。使われ方：標準添加射の単位適合性。 -/
theorem exteriorCochainAugmentationComponent_unit (d : M →ₗ[R] R) :
    exteriorCochainAugmentationComponent (S := S) d 0 (exteriorUnitElement d) = 1 := by
  change exteriorAugmentation (S := S)
    (exteriorCochainInclusion d 0 (exteriorUnitElement d)) = 1
  rw [exteriorUnitElement_inclusion]
  exact map_one _

/-- 概要：標準添加鎖写像の次数0成分は構成した係数射。
方針：mkHomToSingle の標準成分公式を使う。
規約：KST Def3.1。使われ方：通常の係数環への評価の確認。 -/
theorem exteriorKoszulAugmentation_f_zero (d : M →ₗ[R] R)
    (hd : ∀ m, algebraMap R S (d m) = 0) :
    (exteriorKoszulAugmentation d hd).f 0 ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of R S)).hom =
        ModuleCat.ofHom (exteriorCochainAugmentationComponent (S := S) d 0) := by
  simp [exteriorKoszulAugmentation]

/-- 概要：標準添加鎖写像の次数0以外の成分は零。
方針：mkHomToSingle の場合分けを簡約する。
規約：KST Def3.1。使われ方：添加射と単位・積の比較を次数0へ帰着する。 -/
theorem exteriorKoszulAugmentation_f_ne_zero (d : M →ₗ[R] R)
    (hd : ∀ m, algebraMap R S (d m) = 0) (q : ℤ) (hq : q ≠ 0) :
    (exteriorKoszulAugmentation d hd).f q = 0 := by
  simp [exteriorKoszulAugmentation, HomologicalComplex.mkHomToSingle, hq]

end SerrePositivity.KST.DerivedBlowup
