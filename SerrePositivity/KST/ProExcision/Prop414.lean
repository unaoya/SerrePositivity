module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.KST.ProExcision.ConstructionA5Equivariant
public import SerrePositivity.KST.ProExcision.ConjugationEquivariance
public import Mathlib.RingTheory.TwoSidedIdeal.Basic
public import Mathlib.Data.Matrix.Mul

/-!
# Proposition 4.14 の非可換再記述の代数的基礎

概要：結合的な非単位環で右乗法と左行列作用の可換性および中心元の像の両側性を証明する。
方針：右乗法には結合律、両側イデアルには中心性を使い、二つの役割を分ける。
規約：KST Proposition 4.14・Claim 4.15・Lemma 4.16 の非可換再記述。
原典の可換性に代えて a の中心性を明示する。φ(v)=va の順序を固定する。
使われ方：非可換なブロック行列群の帰納法と像上の安定 GL の作用の自明性。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
namespace SerrePositivity.KST.ProExcision
open CategoryTheory
open scoped Matrix
variable {I : Type u} [NonUnitalRing I]

/-- 概要：非単位環の中心元であること。
方針：全ての環の元と可換である条件を明示する。
規約：KST 4.14 の非可換再記述。使われ方：aI の両側イデアル性。 -/
def IsCentralElement (a : I) : Prop := ∀ x : I, a * x = x * a

/-- 概要：右乗法は加法群準同型。
方針：右分配法則を使う。
規約：KST Lemma 4.16 の非可換版 φ(x)=xa。
使われ方：列ベクトルへの右乗法と中心元の像。 -/
def rightMultiplication (a : I) : I →+ I where
  toFun x := x * a
  map_zero' := zero_mul a
  map_add' x y := add_mul x y a

/-- 概要：列ベクトルへの右乗法の加法群準同型。
方針：各成分に同じ右乗法を適用する。
規約：KST Lemma 4.16、可換性も中心性も不要。
使われ方：左行列作用に同変な φ。 -/
def vectorRightMultiplication (ι : Type v) (a : I) : (ι → I) →+ (ι → I) where
  toFun x i := x i * a
  map_zero' := by funext i; exact zero_mul a
  map_add' x y := by funext i; exact add_mul (x i) (y i) a

/-- 概要：左行列作用と列の右乗法は可換。
方針：有限和の右分配と各積の結合律を使う。
規約：KST Lemma 4.16 の非可換版、中心性を仮定しない。
使われ方：M_{n,n}(I) 同変性の各行の計算。 -/
lemma vectorRightMultiplication_mulVec {ι : Type v} {κ : Type w} [Fintype κ]
    (a : I) (M : Matrix ι κ I) (v : κ → I) :
    vectorRightMultiplication ι a (M *ᵥ v) = M *ᵥ (vectorRightMultiplication κ a v) := by
  funext i
  change (∑ j, M i j * v j) * a = ∑ j, M i j * (v j * a)
  simp only [Finset.sum_mul, mul_assoc]

/-- 概要：中心元の左乗法の像は両側イデアル。
方針：加法・負号の保存と、左右の吸収を中心性・結合律から証明する。
規約：KST Proposition 4.14 の非可換版 aI。
使われ方：aI と I の間の群・相対ホモロジーの写像の定義。 -/
def centralMultiplicationIdeal (a : I) (ha : IsCentralElement a) : TwoSidedIdeal I :=
  TwoSidedIdeal.mk' (Set.range (fun x : I ↦ a * x))
    ⟨0, mul_zero a⟩
    (by rintro x y ⟨x, rfl⟩ ⟨y, rfl⟩; exact ⟨x + y, mul_add a x y⟩)
    (by rintro x ⟨x, rfl⟩; exact ⟨-x, mul_neg a x⟩)
    (by
      rintro b y ⟨x, rfl⟩
      exact ⟨b * x, by change a * (b * x) = b * (a * x); rw [← mul_assoc, ha b, mul_assoc]⟩)
    (by
      rintro x b ⟨x, rfl⟩
      exact ⟨x * b, (mul_assoc a x b).symm⟩)

/-- 概要：中心元のイデアルへの所属は左乗法の像であること。
方針：集合による構成の所属条件を使う。
規約：KST 4.14 の aI。使われ方：像から相対写像を因子化する。 -/
lemma mem_centralMultiplicationIdeal (a : I) (ha : IsCentralElement a) (x : I) :
    x ∈ centralMultiplicationIdeal a ha ↔ ∃ y : I, a * y = x := by
  change x ∈ TwoSidedIdeal.mk' _ _ _ _ _ _ ↔ _
  rw [TwoSidedIdeal.mem_mk']
  rfl

/-- 概要：中心元の両側イデアルは右乗法の像でもある。
方針：中心性で各元の積の順序を入れ替える。
規約：KST 4.14・4.16 の aI と φ の向きの整合。
使われ方：右乗法による相対写像の因子化。 -/
lemma mem_centralMultiplicationIdeal_iff_right (a : I) (ha : IsCentralElement a) (x : I) :
    x ∈ centralMultiplicationIdeal a ha ↔ ∃ y : I, y * a = x := by
  rw [mem_centralMultiplicationIdeal]
  constructor
  · rintro ⟨y, hy⟩; exact ⟨y, (ha y).symm.trans hy⟩
  · rintro ⟨y, hy⟩; exact ⟨y, (ha y).trans hy⟩

/-- 概要：中心元の左乗法の単射性は右乗法にも移る。
方針：中心性で二つの関数の値を同定する。
規約：KST 4.14 の次数ごとの非零因子条件。
使われ方：非可換版の仮定を右乗法による φ と整合させる。 -/
lemma rightMultiplication_injective (a : I) (ha : IsCentralElement a)
    (hinj : Function.Injective (fun x : I ↦ a * x)) :
    Function.Injective (rightMultiplication a) := by
  intro x y h
  apply hinj
  change x * a = y * a at h
  rw [← ha x, ← ha y] at h
  exact h

/-- 概要：右乗法は環と指定元の対の射に自然。
方針：非単位環準同型の乗法保存を使う。
規約：KST Lemma 4.16 の (I,a) に関する関手性。
使われ方：単体次数間の作用と φ の自然性。 -/
lemma rightMultiplication_naturality {J : Type v} [NonUnitalRing J]
    (f : I →ₙ+* J) (a : I) (b : J) (hab : f a = b) (x : I) :
    f (rightMultiplication a x) = rightMultiplication b (f x) := by
  change f (x * a) = f x * b
  rw [map_mul, hab]

/-- 概要：列ベクトルの右乗法も環と指定元の対に自然。
方針：各成分で右乗法の自然性を使う。
規約：KST Lemma 4.16、任意の列の添字。
使われ方：単体環上の φ の自然性。 -/
lemma vectorRightMultiplication_naturality {J : Type v} [NonUnitalRing J]
    {ι : Type w} (f : I →ₙ+* J) (a : I) (b : J) (hab : f a = b) (x : ι → I) :
    f ∘ vectorRightMultiplication ι a x = vectorRightMultiplication ι b (f ∘ x) := by
  funext i
  exact rightMultiplication_naturality f a b hab (x i)

/-- 概要：中心元の乗法イデアルは指定元を保つ非単位環準同型で保たれる。
方針：a 倍の表示に準同型を適用する。
規約：KST Proposition 4.14 の非可換再記述、aI の関手性。
使われ方：単体環の各面・退化写像に対する aI の自然性。 -/
lemma centralMultiplicationIdeal_map_mem {J : Type v} [NonUnitalRing J]
    (f : I →ₙ+* J) (a : I) (b : J) (ha : IsCentralElement a) (hb : IsCentralElement b)
    (hab : f a = b) {x : I} (hx : x ∈ centralMultiplicationIdeal a ha) :
    f x ∈ centralMultiplicationIdeal b hb := by
  obtain ⟨y, rfl⟩ := (mem_centralMultiplicationIdeal a ha x).mp hx
  apply (mem_centralMultiplicationIdeal b hb _).mpr
  exact ⟨f y, by rw [map_mul, hab]⟩

end SerrePositivity.KST.ProExcision

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite KST "Eq (4.4)" (partial := component) "仮定：中心元と非単位的単体環の列、ホモロジー模型（Lean が強い）。結論：中心倍イデアルの自然性と列に関する零化。安定 GL(ℤ) のホモロジー像への作用の自明性までは得ない（Lean が弱い）。"] _root_.SerrePositivity.KST.ProExcision.centralMultiplicationIdeal_map_mem
attribute [cite KST "Prop 4.14" (partial := component) "仮定：中心元と非単位的単体環の列、ホモロジー模型（Lean が強い）。結論：中心倍イデアルの自然性と列に関する零化。安定 GL(ℤ) のホモロジー像への作用の自明性までは得ない（Lean が弱い）。"] _root_.SerrePositivity.KST.ProExcision.centralMultiplicationIdeal_map_mem
