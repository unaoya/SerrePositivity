module
public import SerrePositivity.DifferentialGraded.Tensor.KFlatComplex

/-! # 明示的 dg 商の導来比較に用いる片側の局所 K-flat 仮定

全ての x と b に対して同じ向きを選ぶ二条件を分ける。
ここでは比較定理そのものは仮定せず、Hom の A 上の K-flat 性だけを記述する。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 全対象から殺す対象への Hom が A 上 K-flat。 -/
def homIntoKFlat (S : Set D) : Prop :=
  ∀ (x : D) (b : S), complexKFlat A (x ⟶[Complex A] b.val)

/-- 殺す対象から全対象への Hom が A 上 K-flat。 -/
def homOutOfKFlat (S : Set D) : Prop :=
  ∀ (b : S) (x : D), complexKFlat A (b.val ⟶[Complex A] x)

/-- 二つの片側条件のいずれか。組ごとの選言ではない。 -/
def localKFlat (S : Set D) : Prop := homIntoKFlat A D S ∨ homOutOfKFlat A D S

/-- 全 Hom が係数環上 K-flat である条件。 -/
def allHomKFlat : Prop := ∀ x y : D, complexKFlat A (x ⟶[Complex A] y)

lemma homIntoKFlat_mono {S T : Set D} (h : S ⊆ T) (hT : homIntoKFlat A D T) :
    homIntoKFlat A D S := fun x b => hT x ⟨b.val, h b.property⟩

lemma homOutOfKFlat_mono {S T : Set D} (h : S ⊆ T) (hT : homOutOfKFlat A D T) :
    homOutOfKFlat A D S := fun b x => hT ⟨b.val, h b.property⟩ x

lemma localKFlat_mono {S T : Set D} (h : S ⊆ T) (hT : localKFlat A D T) :
    localKFlat A D S :=
  hT.elim (fun hT => Or.inl (homIntoKFlat_mono A D h hT))
    (fun hT => Or.inr (homOutOfKFlat_mono A D h hT))

lemma allHomKFlat_into (h : allHomKFlat A D) (S : Set D) : homIntoKFlat A D S :=
  fun x b => h x b.val

lemma allHomKFlat_outOf (h : allHomKFlat A D) (S : Set D) : homOutOfKFlat A D S :=
  fun b x => h b.val x

lemma allHomKFlat_local (h : allHomKFlat A D) (S : Set D) : localKFlat A D S :=
  Or.inl (allHomKFlat_into A D h S)

/-- Hom ごとの有界範囲は一様でなくてよい。非有界な試験複体に対する K-flat 性を得る。 -/
lemma allHomKFlat_of_flat_bounds
    (a b : D → D → ℤ)
    (ha : ∀ x y i, i < a x y → IsZero ((x ⟶[Complex A] y).X i))
    (hb : ∀ x y i, b x y < i → IsZero ((x ⟶[Complex A] y).X i))
    (hf : ∀ (x y : D) (i : ℤ), Module.Flat A ((x ⟶[Complex A] y).X i)) : allHomKFlat A D :=
  fun x y => complexKFlat_of_flat_bounds A _ (a x y) (b x y) (ha x y) (hb x y) (hf x y)

/-- M9 の商を取る前の dg 圏に適用する、次数零で平坦な Hom の入口。 -/
lemma allHomKFlat_of_flat_degreeZero
    (hz : ∀ (x y : D) (i : ℤ), i ≠ 0 → IsZero ((x ⟶[Complex A] y).X i))
    (hf : ∀ (x y : D) (i : ℤ), Module.Flat A ((x ⟶[Complex A] y).X i)) : allHomKFlat A D :=
  allHomKFlat_of_flat_bounds A D (fun _ _ => 0) (fun _ _ => 0)
    (fun x y i hi => hz x y i (ne_of_lt hi))
    (fun x y i hi => hz x y i (ne_of_gt hi)) hf

/-- 非零次数の平坦性は追加仮定せず、次数零の平坦性だけを要求する M9 用の形。 -/
lemma allHomKFlat_of_flat_zero
    (hz : ∀ (x y : D) (i : ℤ), i ≠ 0 → IsZero ((x ⟶[Complex A] y).X i))
    (hf : ∀ x y : D, Module.Flat A ((x ⟶[Complex A] y).X 0)) : allHomKFlat A D := by
  apply allHomKFlat_of_flat_degreeZero A D hz
  intro x y i
  by_cases hi : i = 0
  · subst i
    exact hf x y
  · have : Subsingleton ((x ⟶[Complex A] y).X i) :=
      ModuleCat.isZero_iff_subsingleton.mp (hz x y i hi)
    infer_instance

end SerrePositivity.DifferentialGraded.DGQuotient
