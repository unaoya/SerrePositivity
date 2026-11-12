module

public import Mathlib.Algebra.Colimit.Ring
public import Mathlib.Algebra.Regular.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# 生の環余極限の関係商と共通指数

## 概要
有向余極限の正則性・指定したねじれ指数・主元剰余と有限関係商の比較を与える。
## 方針
既存の環・加群・実完備化の普遍性と有限段の一意性を使い、単位を保つ比較を構成する。
## 規約
BS 著者版 Proposition 7.10。生の余極限と実完備化を区別し、零環を含む。
## 使われ方
S′ の有界包絡、全有界試験 prism への始性と Corollary 7.3 の比較。
-/

/-! ## DirectLimitUniformBound -/

public noncomputable section
universe u
namespace SerrePositivity
set_option backward.isDefEq.respectTransparency false
variable {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
variable (S : ι → Type u) [∀ i, CommRing (S i)]
variable (f : ∀ i j, i ≤ j → S i →+* S j) [DirectedSystem S (fun i j h => f i j h)]
local notation "L" => Ring.DirectLimit S (fun i j h => f i j h)

/-- 概要：全段に共通の p 冪ねじれ指数は生の環余極限でも有効。
方針：零の等式を後の有限段へ移し、その段の同じ指数で消す。
規約：BS 著者版 Proposition 7.10。遷移の単射性は不要。
使われ方：完備化前の一様な有界ねじれ。 -/
theorem ringDirectLimit_uniform_torsion_bound (p N : ℕ)
    (hN : ∀ i n, ∀ x : S i, (p : S i) ^n * x = 0 → (p : S i) ^N * x = 0)
    (n : ℕ) (x : L) (hx : (p : L) ^n * x = 0) : (p : L) ^N * x = 0 := by
  obtain ⟨i, y, hy⟩ := Ring.DirectLimit.exists_of x
  have hz : Ring.DirectLimit.of S (fun i j h => f i j h) i ((p : S i) ^n * y) = 0 := by
    rw [map_mul, map_pow, map_natCast, hy]
    exact hx
  obtain ⟨j, hij, hj⟩ := Ring.DirectLimit.of.zero_exact hz
  have hnj : (p : S j) ^n * f i j hij y = 0 := by
    simpa only [map_mul, map_pow, map_natCast] using hj
  have hNj := hN j n (f i j hij y) hnj
  rw [← hy, ← Ring.DirectLimit.of_f (G := S) (f := fun i j h => f i j h) hij y]
  rw [← map_natCast (Ring.DirectLimit.of S (fun i j h => f i j h) j) p, ← map_pow, ← map_mul, hNj, map_zero]

/-- 概要：両立する各段の正則元は生の環余極限でも正則。
方針：差を一段に表示し、零の関係を後の段で消す。
規約：BS 著者版 Proposition 7.10 の包絡の分母。遷移の単射性は不要。
使われ方：完備化前の Cartier 生成元。 -/
theorem ringDirectLimit_element_mul_injective (t : ∀ i, S i) (d : L)
    (ht : ∀ i, Ring.DirectLimit.of S (fun i j h => f i j h) i (t i) = d)
    (hcompat : ∀ i j h, f i j h (t i) = t j)
    (hreg : ∀ i, Function.Injective (fun x : S i => t i * x)) :
    Function.Injective (fun x : L => d * x) := by
  intro x y hxy
  change d * x = d * y at hxy
  apply sub_eq_zero.mp
  have hz : d * (x - y) = 0 := by rw [mul_sub, hxy, sub_self]
  obtain ⟨i, z, hi⟩ := Ring.DirectLimit.exists_of (x - y)
  have hz' : Ring.DirectLimit.of S (fun i j h => f i j h) i (t i * z) = 0 := by
    rw [map_mul, ht, hi]
    exact hz
  obtain ⟨j, hij, hj⟩ := Ring.DirectLimit.of.zero_exact hz'
  have hj' : f i j hij z = 0 := by
    apply hreg j
    change t j * f i j hij z = t j * 0
    rw [mul_zero]
    simpa only [map_mul, hcompat] using hj
  rw [← hi, ← Ring.DirectLimit.of_f (G := S) (f := fun i j h => f i j h) hij z, hj', map_zero]

end SerrePositivity

end

/-! ## DirectLimitPrincipalQuotient -/

@[expose] public noncomputable section
universe u
namespace SerrePositivity
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
variable (S : ι → Type u) [∀ i, CommRing (S i)]
variable (f : ∀ i j, i ≤ j → S i →+* S j) [DirectedSystem S (fun i j h => f i j h)]
variable (t : ∀ i, S i) (hcompat : ∀ i j h, f i j h (t i) = t j)

/-- 両立する主元で割った各段の通常商。 -/
abbrev PrincipalQuotientStage (i : ι) := S i ⧸ Ideal.span {t i}

/-- 主元剰余の標準遷移射。 -/
def principalQuotientStageMap {i j : ι} (h : i ≤ j) :
    PrincipalQuotientStage S t i →+* PrincipalQuotientStage S t j :=
  Ideal.quotientMap _ (f i j h) (by
    rw [Ideal.span_singleton_le_iff_mem]
    change f i j h (t i) ∈ Ideal.span {t j}
    rw [hcompat]
    exact Ideal.mem_span_singleton_self _)

/-- 剰余の遷移射は元の段の代表元を写す。 -/
theorem principalQuotientStageMap_mk {i j : ι} (h : i ≤ j) (x : S i) :
    principalQuotientStageMap S f t hcompat h (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (f i j h x) := rfl

/-- 主元剰余の各段は有向系を成す。 -/
instance principalQuotientStageDirectedSystem :
    DirectedSystem (PrincipalQuotientStage S t)
      (fun _ _ h => principalQuotientStageMap S f t hcompat h) where
  map_self {i} x := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [principalQuotientStageMap_mk, DirectedSystem.map_self' f]
  map_map {k j i} h k' x := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [principalQuotientStageMap_mk, principalQuotientStageMap_mk,
      principalQuotientStageMap_mk, DirectedSystem.map_map' f]

local notation "L" => Ring.DirectLimit S (fun i j h => f i j h)
local notation "Q" => PrincipalQuotientStage S t
local notation "qf" => fun i j h => principalQuotientStageMap S f t hcompat h
local notation "LQ" => Ring.DirectLimit Q qf

/-- 概要：主元剰余の生の余極限と、生の余極限の主元剰余は標準同型。
方針：各段の商射を余極限へ延長し、全段の代表元で両逆を確認する。
規約：BS 著者版 Proposition 7.10。遷移の単射性や正則性は不要。
使われ方：包絡余極限の剰余の有界性と平坦性。 -/
theorem exists_ringDirectLimit_principalQuotient_equiv (d : L)
    (ht : ∀ i, Ring.DirectLimit.of S (fun i j h => f i j h) i (t i) = d) :
    ∃ e : (L ⧸ Ideal.span {d}) ≃+* LQ,
      ∀ i (x : S i), e (Ideal.Quotient.mk _ (Ring.DirectLimit.of S (fun i j h => f i j h) i x)) =
        Ring.DirectLimit.of Q qf i (Ideal.Quotient.mk _ x) := by
  let α : L →+* LQ := Ring.DirectLimit.lift S (fun i j h => f i j h) LQ
    (fun i => (Ring.DirectLimit.of Q qf i).comp (Ideal.Quotient.mk _)) (by
      intro i j h x
      exact Ring.DirectLimit.of_f (G := Q) (f := qf) h (Ideal.Quotient.mk _ x))
  have hα (i) (x : S i) : α (Ring.DirectLimit.of S (fun i j h => f i j h) i x) =
      Ring.DirectLimit.of Q qf i (Ideal.Quotient.mk _ x) := Ring.DirectLimit.lift_of _ _ _ i x
  have hαd : α d = 0 := by
    let i := Classical.choice (inferInstance : Nonempty ι)
    rw [← ht i, hα, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _), map_zero]
  let α' : (L ⧸ Ideal.span {d}) →+* LQ := Ideal.Quotient.lift _ α
    ((Ideal.span_singleton_le_iff_mem (RingHom.ker α)).mpr hαd)
  let βi (i : ι) : Q i →+* (L ⧸ Ideal.span {d}) :=
    Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp (Ring.DirectLimit.of S (fun i j h => f i j h) i)) (by
      change Ideal.span {t i} ≤ RingHom.ker ((Ideal.Quotient.mk _).comp
        (Ring.DirectLimit.of S (fun i j h => f i j h) i))
      rw [Ideal.span_singleton_le_iff_mem]
      change Ideal.Quotient.mk _ (Ring.DirectLimit.of S (fun i j h => f i j h) i (t i)) = 0
      rw [ht]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _))
  let β : LQ →+* (L ⧸ Ideal.span {d}) := Ring.DirectLimit.lift Q qf _ βi (by
    intro i j h x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk _ (Ring.DirectLimit.of S (fun i j h => f i j h) j (f i j h x)) = _
    rw [Ring.DirectLimit.of_f]
    rfl)
  have hβα : β.comp α' = RingHom.id _ := by
    apply Ideal.Quotient.ringHom_ext
    apply Ring.DirectLimit.hom_ext
    intro i
    apply RingHom.ext
    intro x
    change β (α (Ring.DirectLimit.of S (fun i j h => f i j h) i x)) = _
    rw [hα]
    exact Ring.DirectLimit.lift_of (G := Q) (f := qf) _ βi _ i (Ideal.Quotient.mk _ x)
  have hαβ : α'.comp β = RingHom.id _ := by
    apply Ring.DirectLimit.hom_ext
    intro i
    apply Ideal.Quotient.ringHom_ext
    apply RingHom.ext
    intro x
    change α' (β (Ring.DirectLimit.of Q qf i (Ideal.Quotient.mk _ x))) = _
    rw [Ring.DirectLimit.lift_of]
    exact hα i x
  exact ⟨RingEquiv.ofRingHom α' β hαβ hβα, hα⟩

end SerrePositivity

end

/-! ## FiniteRelationColimit -/

@[expose] public noncomputable section
universe u
namespace SerrePositivity
set_option backward.isDefEq.respectTransparency false
variable {A J : Type u} [CommRing A] (a : J → A)

/-- 有限部分族で生成される関係イデアル。 -/
def finiteRelationIdeal (F : Finset J) : Ideal A := Ideal.span (a '' (F : Set J))

/-- 有限関係の通常商。 -/
abbrev FiniteRelationStage (F : Finset J) := A ⧸ finiteRelationIdeal a F

/-- 有限関係のイデアルは部分族に関して単調。 -/
theorem finiteRelationIdeal_mono {F G : Finset J} (h : F ⊆ G) :
    finiteRelationIdeal a F ≤ finiteRelationIdeal a G :=
  Ideal.span_mono (Set.image_mono h)

/-- 有限関係商の遷移射。 -/
def finiteRelationMap {F G : Finset J} (h : F ⊆ G) :
    FiniteRelationStage a F →+* FiniteRelationStage a G :=
  Ideal.quotientMap _ (RingHom.id A) (by simpa using finiteRelationIdeal_mono a h)

/-- 有限関係商の遷移射は通常の商の単位を保つ。 -/
theorem finiteRelationMap_mk {F G : Finset J} (h : F ⊆ G) (x : A) :
    finiteRelationMap a h (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ x := rfl

/-- 有限関係商は有向系を成す。 -/
instance finiteRelationDirectedSystem :
    DirectedSystem (FiniteRelationStage a) (fun _ _ h => finiteRelationMap a h) where
  map_self {i} x := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  map_map {k j i} h k' x := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl

/-- 有限関係商の生の環余極限。 -/
abbrev FiniteRelationColimit :=
  Ring.DirectLimit (FiniteRelationStage a) (fun _ _ h => finiteRelationMap a h)

/-- 各有限段の生の余極限への射。 -/
def finiteRelationColimitOf (F : Finset J) : FiniteRelationStage a F →+* FiniteRelationColimit a :=
  Ring.DirectLimit.of _ _ F

/-- 生の余極限の係数射は空関係の段から作る。 -/
def finiteRelationColimitBase : A →+* FiniteRelationColimit a :=
  (finiteRelationColimitOf a ∅).comp (Ideal.Quotient.mk _)

/-- 生の余極限の係数射はどの有限段から計算しても同じ。 -/
theorem finiteRelationColimitBase_eq_stage (F : Finset J) (x : A) :
    finiteRelationColimitBase a x = finiteRelationColimitOf a F (Ideal.Quotient.mk _ x) :=
  (Ring.DirectLimit.of_f (G := FiniteRelationStage a)
    (f := fun _ _ h => finiteRelationMap a h) (Finset.empty_subset F)
    (Ideal.Quotient.mk _ x)).symm

/-- 生の余極限では全ての指定関係が零になる。 -/
theorem finiteRelationColimitBase_relation (j : J) : finiteRelationColimitBase a (a j) = 0 := by
  classical
  rw [finiteRelationColimitBase_eq_stage a {j}]
  have hz : Ideal.Quotient.mk (finiteRelationIdeal a {j}) (a j) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨j, by simp, rfl⟩)
  rw [hz, map_zero]

/-- 全関係の通常商から生の余極限への射。 -/
def finiteRelationFullToColimit : (A ⧸ Ideal.span (Set.range a)) →+* FiniteRelationColimit a :=
  Ideal.Quotient.lift _ (finiteRelationColimitBase a) (by
    change Ideal.span (Set.range a) ≤ RingHom.ker (finiteRelationColimitBase a)
    rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    exact finiteRelationColimitBase_relation a j)

/-- 各有限段から全関係の通常商への射。 -/
def finiteRelationToFull (F : Finset J) : FiniteRelationStage a F →+* (A ⧸ Ideal.span (Set.range a)) :=
  Ideal.quotientMap _ (RingHom.id A) (by
    change finiteRelationIdeal a F ≤ Ideal.span (Set.range a)
    apply Ideal.span_mono
    rintro _ ⟨j, _, rfl⟩
    exact ⟨j, rfl⟩)

/-- 生の余極限から全関係の通常商への射。 -/
def finiteRelationColimitToFull : FiniteRelationColimit a →+* (A ⧸ Ideal.span (Set.range a)) :=
  Ring.DirectLimit.lift _ _ _ (finiteRelationToFull a) (by
    intro F G h x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl)

/-- 余極限からの標準射は有限段の標準商射を延長する。 -/
theorem finiteRelationColimitToFull_of (F : Finset J) (x : FiniteRelationStage a F) :
    finiteRelationColimitToFull a (finiteRelationColimitOf a F x) = finiteRelationToFull a F x :=
  Ring.DirectLimit.lift_of _ _ _ F x

/-- 概要：全関係の通常商は有限部分族商の生の環余極限と同型。
方針：商と余極限上で両方向の合成を検証する。
規約：BS 著者版 Proposition 7.10。実完備化前の同型。
使われ方：S′ の完備余極限との比較の第一段。 -/
def finiteRelationColimitEquiv : FiniteRelationColimit a ≃+* (A ⧸ Ideal.span (Set.range a)) := by
  apply RingEquiv.ofRingHom (finiteRelationColimitToFull a) (finiteRelationFullToColimit a)
  · apply Ideal.Quotient.ringHom_ext
    apply RingHom.ext
    intro x
    exact finiteRelationColimitToFull_of a ∅ (Ideal.Quotient.mk _ x)
  · apply Ring.DirectLimit.hom_ext
    intro F
    apply Ideal.Quotient.ringHom_ext
    apply RingHom.ext
    intro x
    change finiteRelationFullToColimit a
      (finiteRelationColimitToFull a (finiteRelationColimitOf a F (Ideal.Quotient.mk _ x))) = _
    rw [finiteRelationColimitToFull_of]
    exact finiteRelationColimitBase_eq_stage a F x

end SerrePositivity

end
