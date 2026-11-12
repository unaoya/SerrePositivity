module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Order.Fin.SuccAboveOrderIso
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Order.Fin.Basic

/-!
概要：有限交叉の図式から作る全タプル版と狭義増加版の Čech 項と余境界。
方針：タプルの像を添字集合とし、面を取るときは部分集合に沿って制限する。
規約：添字の自然数はタプルの長さ。長さ零を増大項にも使える。
使われ方：標準開の局所化図式に適用し、狭義増加版で有界性を得る。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open CategoryTheory
open scoped BigOperators

variable {R : Type*} [CommRing R] {ι : Type*} [DecidableEq ι]

/-- タプルに現れる添字の有限集合。 -/
def cechTupleSupport {k : ℕ} (t : Fin k → ι) : Finset ι :=
  Finset.univ.image t

/-- タプルの再添字付けで、その添字集合は増えない。 -/
theorem cechTupleSupport_comp_subset {k l : ℕ} (t : Fin l → ι) (f : Fin k → Fin l) :
    cechTupleSupport (t ∘ f) ⊆ cechTupleSupport t := by
  intro a ha
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp ha
  exact Finset.mem_image.mpr ⟨f j, Finset.mem_univ _, rfl⟩

/-- 面の添字集合は元のタプルの添字集合に含まれる。 -/
theorem cechTupleSupport_face_subset {k : ℕ} (t : Fin (k + 1) → ι) (i : Fin (k + 1)) :
    cechTupleSupport (t ∘ i.succAbove) ⊆ cechTupleSupport t :=
  cechTupleSupport_comp_subset t i.succAbove

/-- タプルの先頭に付けた頂点が、添字集合に追加される。 -/
theorem cechTupleSupport_cons {k : ℕ} (v : ι) (t : Fin k → ι) :
    cechTupleSupport (Fin.cons v t) = insert v (cechTupleSupport t) := by
  ext a
  simp only [cechTupleSupport, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert]
  constructor
  · rintro ⟨j, rfl⟩
    refine Fin.cases ?_ (fun i ↦ ?_) j
    · simp
    · exact Or.inr ⟨i, by simp⟩
  · rintro (rfl | ⟨j, rfl⟩)
    · exact ⟨0, by simp⟩
    · exact ⟨j.succ, by simp⟩

/--
概要：負の指数の台 N の外の頂点を先頭に追加しても、その単項式が現れる条件は変わらない。
方針：追加した一つの頂点を N が含まないことを使う。
規約：単項式がチャートに現れる条件は N が添字集合に含まれること。
使われ方：単項式ごとの Čech コチェインを先頭追加で縮約する。
-/
theorem cechTupleSupport_cons_contains_iff {k : ℕ} {N : Finset ι} {v : ι}
    (hv : v ∉ N) (t : Fin k → ι) :
    N ⊆ cechTupleSupport (Fin.cons v t) ↔ N ⊆ cechTupleSupport t := by
  rw [cechTupleSupport_cons]
  constructor
  · intro h a ha
    rcases Finset.mem_insert.mp (h ha) with rfl | ha'
    · exact (hv ha).elim
    · exact ha'
  · intro h a ha
    exact Finset.mem_insert_of_mem (h ha)

/-- 一つの Laurent 単項式に対応する、指定の台を持つコチェインの部分加群。 -/
def projectiveMonomialCochains (N : Finset ι) (k : ℕ) : Submodule R ((Fin k → ι) → R) where
  carrier := {a | ∀ t, ¬ N ⊆ cechTupleSupport t → a t = 0}
  zero_mem' := by simp
  add_mem' ha hb := fun t ht ↦ by simp [ha t ht, hb t ht]
  smul_mem' r a ha := fun t ht ↦ by simp [ha t ht]

/-- 一つの Laurent 単項式に対応する余境界。 -/
def projectiveMonomialDifferential (N : Finset ι) (k : ℕ) :
    projectiveMonomialCochains (R := R) N k →ₗ[R]
      projectiveMonomialCochains (R := R) N (k + 1) := by
  let d : (projectiveMonomialCochains (R := R) N k) →ₗ[R] (Fin (k + 1) → ι) → R :=
    LinearMap.pi fun t ↦ ∑ i : Fin (k + 1), (-1 : ℤ) ^ i.val •
      (LinearMap.proj (t ∘ i.succAbove)).comp (projectiveMonomialCochains (R := R) N k).subtype
  refine LinearMap.codRestrict _ d fun a t ht ↦ ?_
  simp only [d, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, LinearMap.proj_apply, Submodule.subtype_apply]
  apply Finset.sum_eq_zero
  intro i _
  rw [a.property _ (fun h ↦ ht (h.trans (cechTupleSupport_face_subset t i))), smul_zero]

/-- 台の外の頂点を先頭に付けて評価する。 -/
def projectiveMonomialContraction (N : Finset ι) (v : ι) (hv : v ∉ N) (k : ℕ) :
    projectiveMonomialCochains (R := R) N (k + 1) →ₗ[R]
      projectiveMonomialCochains (R := R) N k := by
  let h : (projectiveMonomialCochains (R := R) N (k + 1)) →ₗ[R] (Fin k → ι) → R :=
    LinearMap.pi fun t ↦
      (LinearMap.proj (Fin.cons v t)).comp (projectiveMonomialCochains (R := R) N (k + 1)).subtype
  exact LinearMap.codRestrict _ h fun a t ht ↦
    a.property _ (fun e ↦ ht ((cechTupleSupport_cons_contains_iff hv t).mp e))

private theorem projectiveMonomialContraction_apply (N : Finset ι) (v : ι)
    (hv : v ∉ N) (k : ℕ) (a : projectiveMonomialCochains (R := R) N (k + 1))
    (t : Fin k → ι) :
    (projectiveMonomialContraction N v hv k a).val t = a.val (Fin.cons v t) := rfl

/-- 一つの単項式の余境界を、タプルの各面で評価する。 -/
theorem projectiveMonomialDifferential_apply (N : Finset ι) (k : ℕ)
    (a : projectiveMonomialCochains (R := R) N k) (t : Fin (k + 1) → ι) :
    (projectiveMonomialDifferential N k a).val t =
      ∑ i : Fin (k + 1), (-1 : ℤ) ^ i.val • a.val (t ∘ i.succAbove) := by
  change ((∑ i : Fin (k + 1), (-1 : ℤ) ^ i.val •
    (LinearMap.proj (t ∘ i.succAbove)).comp
      (projectiveMonomialCochains (R := R) N k).subtype) a) = _
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, Submodule.subtype_apply]

/--
概要：負の指数の台が全体より小さければ、全タプルの単項式コチェインは縮約する。
方針：先頭を削除する項を分け、残った削除の符号を反転する。
規約：長さ一の式には長さ零の増大項が入る。
使われ方：射影空間の捻りでコホモロジーに寄与しない単項式を除く。
-/
theorem projectiveMonomialContraction_identity (N : Finset ι) (v : ι) (hv : v ∉ N)
    (k : ℕ) :
    (projectiveMonomialContraction (R := R) N v hv (k + 1)).comp
      (projectiveMonomialDifferential N (k + 1)) +
    (projectiveMonomialDifferential N k).comp (projectiveMonomialContraction N v hv k) =
      LinearMap.id := by
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  funext t
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply, Submodule.coe_add,
    Pi.add_apply, projectiveMonomialContraction_apply, projectiveMonomialDifferential_apply]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.succAbove_zero, Fin.cons_comp_succ,
    Fin.val_succ, pow_succ, mul_neg_one, neg_smul, Fin.cons_comp_succ_succAbove,
    Finset.sum_neg_distrib, add_assoc]
  have hface (i : Fin (k + 1)) : i.removeNth t = t ∘ i.succAbove := rfl
  simp only [hface, neg_add_cancel, add_zero]

/-- 全タプルを添字とする Čech の項。 -/
abbrev FullCechCochains (D : Finset ι ⥤ ModuleCat R) (k : ℕ) :=
  (t : Fin k → ι) → D.obj (cechTupleSupport t)

/--
概要：整数係数のタプル鎖を、指定の交叉上でコチェインに評価する。
方針：各タプルの成分を取り、添字集合の包含で制限した値の整数線形結合を取る。
規約：指定した添字集合に含まれないタプルは零で評価する。
使われ方：頂点集合を保つ鎖ホモトピーを、制限写像付きの Čech コチェインへ移す。
-/
def fullCechEvaluateAt (D : Finset ι ⥤ ModuleCat R) (k : ℕ) (s : Finset ι) :
    ((Fin k → ι) →₀ ℤ) →ₗ[ℤ] (FullCechCochains D k →ₗ[R] D.obj s) :=
  Finsupp.linearCombination ℤ fun t ↦
    if h : cechTupleSupport t ⊆ s then
      (D.map (homOfLE h)).hom.comp (LinearMap.proj t)
    else 0

/-- 一つのタプル上の評価は、その成分の制限写像で与えられる。 -/
theorem fullCechEvaluateAt_single (D : Finset ι ⥤ ModuleCat R) {k : ℕ} {s : Finset ι}
    {t : Fin k → ι} (ht : cechTupleSupport t ⊆ s) :
    fullCechEvaluateAt D k s (Finsupp.single t 1) =
      (D.map (homOfLE ht)).hom.comp (LinearMap.proj t) := by
  simp [fullCechEvaluateAt, ht]

/--
概要：タプル鎖の評価は、各成分の頂点が入る交叉から、より小さい開への制限と可換。
方針：鎖を台上の和に展開し、各成分に制限の合成則を使う。
規約：交叉は添字集合で表すので、制限はその集合を広げる向き。
使われ方：支持を保つ鎖写像の合成を、Čech コチェイン上で転置する。
-/
theorem fullCechEvaluateAt_restrict (D : Finset ι ⥤ ModuleCat R) {k : ℕ}
    {s t : Finset ι} (hst : s ⊆ t) (x : (Fin k → ι) →₀ ℤ)
    (hx : ∀ u ∈ x.support, cechTupleSupport u ⊆ s) (a : FullCechCochains D k) :
    (D.map (homOfLE hst)).hom (fullCechEvaluateAt D k s x a) =
      fullCechEvaluateAt D k t x a := by
  unfold fullCechEvaluateAt
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, LinearMap.sum_apply,
    LinearMap.smul_apply, map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro u hu
  have hs := hx u hu
  simp only [dite_eq_left hs, dite_eq_left (hs.trans hst), LinearMap.comp_apply,
    LinearMap.proj_apply]
  congr 1
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← D.map_comp]
  rfl

/-- タプル鎖の線形写像を制限写像付きコチェインへ転置する。 -/
def fullCechTranspose (D : Finset ι ⥤ ModuleCat R) {k l : ℕ}
    (P : ((Fin l → ι) →₀ ℤ) →ₗ[ℤ] (Fin k → ι) →₀ ℤ) :
    FullCechCochains D k →ₗ[R] FullCechCochains D l :=
  LinearMap.pi fun t ↦ fullCechEvaluateAt D k (cechTupleSupport t) (P (Finsupp.single t 1))

/-- 恒等な鎖写像の転置は恒等写像。 -/
theorem fullCechTranspose_id (D : Finset ι ⥤ ModuleCat R) (k : ℕ) :
    fullCechTranspose D (LinearMap.id : ((Fin k → ι) →₀ ℤ) →ₗ[ℤ] _) = LinearMap.id := by
  apply LinearMap.ext
  intro a
  funext t
  change fullCechEvaluateAt D k (cechTupleSupport t) (Finsupp.single t 1) a = a t
  rw [fullCechEvaluateAt_single D le_rfl]
  change (D.map (𝟙 (cechTupleSupport t))).hom (a t) = a t
  rw [D.map_id]
  rfl

/-- 制限写像の交代和による全タプル版の余境界。 -/
def fullCechDifferential (D : Finset ι ⥤ ModuleCat R) (k : ℕ) :
    FullCechCochains D k →ₗ[R] FullCechCochains D (k + 1) :=
  LinearMap.pi fun t ↦
    ∑ i : Fin (k + 1), (-1 : ℤ) ^ i.val •
      (D.map (homOfLE (cechTupleSupport_face_subset t i))).hom.comp
        (LinearMap.proj (t ∘ i.succAbove))

/-- 全タプル版の余境界の成分は、制限した面の値の交代和。 -/
theorem fullCechDifferential_apply (D : Finset ι ⥤ ModuleCat R) (k : ℕ)
    (a : FullCechCochains D k) (t : Fin (k + 1) → ι) :
    fullCechDifferential D k a t =
      ∑ i : Fin (k + 1), (-1 : ℤ) ^ i.val •
        (D.map (homOfLE (cechTupleSupport_face_subset t i))).hom (a (t ∘ i.succAbove)) := by
  unfold fullCechDifferential
  rw [LinearMap.pi_apply, LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply]

/-- 有限交叉上の係数を、タプルの添字写像で引き戻す。 -/
def fullCechReindex (D : Finset ι ⥤ ModuleCat R) {k l : ℕ} (f : Fin k → Fin l) :
    FullCechCochains D k →ₗ[R] FullCechCochains D l :=
  LinearMap.pi fun t ↦
    (D.map (homOfLE (cechTupleSupport_comp_subset t f))).hom.comp (LinearMap.proj (t ∘ f))

/-- 全タプル版の余単体加群。 -/
def fullCechCosimplicial (D : Finset ι ⥤ ModuleCat R) : CosimplicialObject (ModuleCat R) where
  obj n := ModuleCat.of R (FullCechCochains D (n.len + 1))
  map f := ModuleCat.ofHom (fullCechReindex D f.toOrderHom)
  map_id n := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    funext t
    change (D.map (𝟙 (cechTupleSupport t))).hom (a t) = a t
    rw [D.map_id]
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    funext t
    change (D.map (homOfLE (cechTupleSupport_comp_subset t
        (g.toOrderHom ∘ f.toOrderHom)))).hom (a (t ∘ g.toOrderHom ∘ f.toOrderHom)) =
      (D.map (homOfLE (cechTupleSupport_comp_subset t g.toOrderHom))).hom
        ((D.map (homOfLE (cechTupleSupport_comp_subset (t ∘ g.toOrderHom) f.toOrderHom))).hom
          (a (t ∘ g.toOrderHom ∘ f.toOrderHom)))
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← D.map_comp]
    rfl

private theorem fullCechCosimplicial_objD (D : Finset ι ⥤ ModuleCat R) (k : ℕ) :
    (AlgebraicTopology.AlternatingCofaceMapComplex.objD (fullCechCosimplicial D) k).hom =
      fullCechDifferential D (k + 1) := by
  apply LinearMap.ext
  intro a
  funext t
  have hd (i : Fin (k + 2)) :
      ((fullCechCosimplicial D).δ i).hom = fullCechReindex D i.succAbove := rfl
  simp only [AlgebraicTopology.AlternatingCofaceMapComplex.objD, ModuleCat.hom_sum,
    ModuleCat.hom_zsmul, hd]
  have he (b : FullCechCochains D (k + 1)) (u : Fin (k + 2) → ι) :
      (∑ i : Fin (k + 2), (-1 : ℤ) ^ i.val • fullCechReindex D i.succAbove) b u =
        fullCechDifferential D (k + 1) b u := by
    rw [fullCechDifferential_apply, LinearMap.sum_apply, Finset.sum_apply]
    simp only [LinearMap.smul_apply, Pi.smul_apply, fullCechReindex,
      LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  exact he a t

/-- 通常の Čech 次数では全タプル版の余境界の二乗が零になる。 -/
theorem fullCechDifferential_squared (D : Finset ι ⥤ ModuleCat R) (k : ℕ) :
    (fullCechDifferential D (k + 2)).comp (fullCechDifferential D (k + 1)) = 0 := by
  have h := congrArg ModuleCat.Hom.hom
    (AlgebraicTopology.AlternatingCofaceMapComplex.d_squared (fullCechCosimplicial D) k)
  rw [ModuleCat.hom_comp, ModuleCat.hom_zero, fullCechCosimplicial_objD,
    fullCechCosimplicial_objD] at h
  exact h

/-- 通常の全タプル Čech 複体。次数 q では長さ q + 1 のタプルを使う。 -/
def fullCechComplex (D : Finset ι ⥤ ModuleCat R) : CochainComplex (ModuleCat R) ℕ :=
  CochainComplex.of (fun q ↦ ModuleCat.of R (FullCechCochains D (q + 1)))
    (fun q ↦ ModuleCat.ofHom (fullCechDifferential D (q + 1))) (by
      intro q
      apply ModuleCat.hom_ext
      simpa [ModuleCat.hom_comp] using fullCechDifferential_squared D q)

section Ordered

variable [LinearOrder ι]

/-- 狭義増加タプルを添字とする Čech の項。 -/
abbrev OrderedCechCochains (D : Finset ι ⥤ ModuleCat R) (k : ℕ) :=
  (t : {t : Fin k → ι // StrictMono t}) → D.obj (cechTupleSupport t.val)

/-- 狭義増加タプルだけを使う余境界。 -/
def orderedCechDifferential (D : Finset ι ⥤ ModuleCat R) (k : ℕ) :
    OrderedCechCochains D k →ₗ[R] OrderedCechCochains D (k + 1) :=
  LinearMap.pi fun t ↦
    ∑ i : Fin (k + 1),
      let face : {u : Fin k → ι // StrictMono u} :=
        ⟨t.val ∘ i.succAbove, t.property.comp (Fin.strictMono_succAbove i)⟩
      (-1 : ℤ) ^ i.val •
        (D.map (homOfLE (cechTupleSupport_face_subset t.val i))).hom.comp (LinearMap.proj face)

/-- 狭義増加版は添字集合の濃度より長いタプルを持たない。 -/
theorem subsingleton_orderedCechCochains [Fintype ι] (D : Finset ι ⥤ ModuleCat R)
    (k : ℕ) (hk : Fintype.card ι < k) : Subsingleton (OrderedCechCochains D k) :=
  ⟨fun _ _ ↦ funext fun t ↦ by
    have h := Fintype.card_le_of_injective t.val t.property.injective
    rw [Fintype.card_fin] at h
    exact (Nat.not_le.mpr hk h).elim⟩

/-- 全タプル版を狭義増加タプルの成分へ制限する。 -/
def fullCechRestrictOrdered (D : Finset ι ⥤ ModuleCat R) (k : ℕ) :
    FullCechCochains D k →ₗ[R] OrderedCechCochains D k :=
  LinearMap.pi fun t ↦ LinearMap.proj t.val

/-- 成分の制限は余境界と可換になる。 -/
theorem fullCechRestrictOrdered_comp_differential (D : Finset ι ⥤ ModuleCat R) (k : ℕ) :
    (fullCechRestrictOrdered D (k + 1)).comp (fullCechDifferential D k) =
      (orderedCechDifferential D k).comp (fullCechRestrictOrdered D k) := by
  apply LinearMap.ext
  intro a
  funext t
  simp [fullCechRestrictOrdered, fullCechDifferential, orderedCechDifferential,
    LinearMap.sum_apply]

/-- 狭義増加版への成分の制限は全射。 -/
theorem fullCechRestrictOrdered_surjective (D : Finset ι ⥤ ModuleCat R) (k : ℕ) :
    Function.Surjective (fullCechRestrictOrdered D k) := by
  classical
  intro a
  let b : FullCechCochains D k := fun t ↦ if h : StrictMono t then a ⟨t, h⟩ else 0
  exact ⟨b, funext fun t ↦ by simp [fullCechRestrictOrdered, b, t.property]⟩

/-- 通常の Čech 次数では狭義増加版の余境界の二乗が零になる。 -/
theorem orderedCechDifferential_squared (D : Finset ι ⥤ ModuleCat R) (k : ℕ) :
    (orderedCechDifferential D (k + 2)).comp (orderedCechDifferential D (k + 1)) = 0 := by
  apply LinearMap.ext
  intro a
  obtain ⟨b, rfl⟩ := fullCechRestrictOrdered_surjective D (k + 1) a
  have comm (n : ℕ) (c : FullCechCochains D n) :
      fullCechRestrictOrdered D (n + 1) (fullCechDifferential D n c) =
        orderedCechDifferential D n (fullCechRestrictOrdered D n c) :=
    LinearMap.congr_fun (fullCechRestrictOrdered_comp_differential D n) c
  change orderedCechDifferential D (k + 2)
    (orderedCechDifferential D (k + 1) (fullCechRestrictOrdered D (k + 1) b)) = 0
  rw [← comm (k + 1) b, ← comm (k + 2) (fullCechDifferential D (k + 1) b)]
  have h := LinearMap.congr_fun (fullCechDifferential_squared D k) b
  change fullCechDifferential D (k + 2) (fullCechDifferential D (k + 1) b) = 0 at h
  rw [h, map_zero]

/-- 狭義増加タプルによる通常の Čech 複体。 -/
def orderedCechComplex (D : Finset ι ⥤ ModuleCat R) :
    CochainComplex (ModuleCat R) ℕ :=
  CochainComplex.of (fun q ↦ ModuleCat.of R (OrderedCechCochains D (q + 1)))
    (fun q ↦ ModuleCat.ofHom (orderedCechDifferential D (q + 1))) (by
      intro q
      apply ModuleCat.hom_ext
      simpa [ModuleCat.hom_comp] using orderedCechDifferential_squared D q)

/-- 全タプル版から狭義増加版への成分制限をコチェイン写像にまとめる。 -/
def fullCechComplexRestrictOrdered (D : Finset ι ⥤ ModuleCat R) :
    fullCechComplex D ⟶ orderedCechComplex D :=
  CochainComplex.ofHom (fun q ↦ ModuleCat.ofHom (fullCechRestrictOrdered D (q + 1))) (by
    intro q
    change ModuleCat.ofHom (fullCechRestrictOrdered D (q + 1)) ≫
        (orderedCechComplex D).d q (q + 1) =
      (fullCechComplex D).d q (q + 1) ≫
        ModuleCat.ofHom (fullCechRestrictOrdered D (q + 2))
    simp only [orderedCechComplex, fullCechComplex, CochainComplex.of_d]
    apply ModuleCat.hom_ext
    simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom] using
      (fullCechRestrictOrdered_comp_differential D (q + 1)).symm)

/-- 被覆の添字集合の濃度以上の次数で、狭義増加版のコホモロジーは消える。 -/
theorem isZero_orderedCechHomology [Fintype ι] (D : Finset ι ⥤ ModuleCat R)
    (q : ℕ) (hq : Fintype.card ι ≤ q) :
    Limits.IsZero ((orderedCechComplex D).homology q) := by
  apply ShortComplex.isZero_homology_of_isZero_X₂
  exact ModuleCat.isZero_of_iff_subsingleton.mpr
    (subsingleton_orderedCechCochains D (q + 1) (Nat.lt_succ_of_le hq))

omit [LinearOrder ι] in
/-- 単射なタプルの添字集合の濃度はタプルの長さに等しい。 -/
theorem cechTupleSupport_card {k : ℕ} {t : Fin k → ι} (ht : Function.Injective t) :
    (cechTupleSupport t).card = k := by
  rw [cechTupleSupport, Finset.card_image_of_injective _ ht, Finset.card_univ, Fintype.card_fin]

/-- 単射なタプルを、その添字集合への全単射と見なす。 -/
def cechTupleSupportEquiv {k : ℕ} (t : Fin k → ι) (ht : Function.Injective t) :
    Fin k ≃ cechTupleSupport t :=
  Equiv.ofBijective (fun i ↦ ⟨t i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩) (by
    constructor
    · intro i j h
      exact ht (congrArg Subtype.val h)
    · rintro ⟨a, ha⟩
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ha
      exact ⟨i, rfl⟩)

/-- 整列順の位置を元のタプルの位置に移す置換。 -/
def cechTupleSortingPerm {k : ℕ} (t : Fin k → ι) (ht : Function.Injective t) :
    Equiv.Perm (Fin k) :=
  ((cechTupleSupport t).orderIsoOfFin (cechTupleSupport_card ht)).toEquiv.trans
    (cechTupleSupportEquiv t ht).symm

/-- タプルを整列置換で引き戻すと、添字集合の増加列になる。 -/
theorem cechTupleSortingPerm_apply {k : ℕ} (t : Fin k → ι) (ht : Function.Injective t)
    (j : Fin k) :
    t (cechTupleSortingPerm t ht j) = (cechTupleSupport t).orderEmbOfFin
      (cechTupleSupport_card ht) j :=
  congrArg Subtype.val ((cechTupleSupportEquiv t ht).apply_symm_apply _)

/-- 既に狭義増加なタプルの整列置換は恒等である。 -/
theorem cechTupleSortingPerm_eq_one {k : ℕ} (t : Fin k → ι) (ht : StrictMono t) :
    cechTupleSortingPerm t ht.injective = 1 := by
  apply Equiv.ext
  intro j
  apply ht.injective
  have e : t = (cechTupleSupport t).orderEmbOfFin (cechTupleSupport_card ht.injective) :=
    Finset.orderEmbOfFin_unique _ (fun i ↦ Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩) ht
  exact (cechTupleSortingPerm_apply t ht.injective j).trans (congrFun e j).symm

/-- 狭義増加版の値を整列の符号付きで全タプルへ延長する。 -/
def orderedCechExtendFull (D : Finset ι ⥤ ModuleCat R) (k : ℕ) :
    OrderedCechCochains D k →ₗ[R] FullCechCochains D k := by
  classical
  apply LinearMap.pi
  intro t
  if ht : Function.Injective t then
    let T := cechTupleSupport t
    let v := T.orderEmbOfFin (cechTupleSupport_card ht)
    have hs : cechTupleSupport v = T := by
      apply Finset.coe_injective
      rw [cechTupleSupport, Finset.coe_image, Finset.coe_univ, Set.image_univ]
      exact T.range_orderEmbOfFin (cechTupleSupport_card ht)
    let ordered : {u : Fin k → ι // StrictMono u} := ⟨v, v.strictMono⟩
    exact (cechTupleSortingPerm t ht).sign.val •
      (D.map (eqToHom hs)).hom.comp (LinearMap.proj ordered)
  else
    exact 0

end Ordered

/-- 置換から一つの位置とその像を除いて得られる置換。 -/
def cechPermDelete {k : ℕ} (σ : Equiv.Perm (Fin (k + 2))) (i : Fin (k + 2)) :
    Equiv.Perm (Fin (k + 1)) :=
  (i.succAboveOrderIso.toEquiv.trans (σ.subtypeEquiv (by
    intro j
    change j ∈ ({i}ᶜ : Finset _) ↔ σ j ∈ ({σ i}ᶜ : Finset _)
    simp only [Finset.mem_compl, Finset.mem_singleton, Equiv.apply_eq_iff_eq]))).trans
      (σ i).succAboveOrderIso.toEquiv.symm

/-- 一つの位置を削除した置換は、削除する前の置換と残った位置で可換になる。 -/
theorem cechPermDelete_apply {k : ℕ} (σ : Equiv.Perm (Fin (k + 2)))
    (i : Fin (k + 2)) (j : Fin (k + 1)) :
    (σ i).succAbove (cechPermDelete σ i j) = σ (i.succAbove j) := by
  exact congrArg Subtype.val ((σ i).succAboveOrderIso.toEquiv.apply_symm_apply _)

/-- 削除した位置とその像の符号を、制限置換の符号に移す。 -/
theorem cechPermDelete_sign {k : ℕ} (σ : Equiv.Perm (Fin (k + 2))) (i : Fin (k + 2)) :
    σ.sign * (-1) ^ i.val = (-1) ^ (σ i).val * (cechPermDelete σ i).sign := by
  have e : σ * Equiv.Perm.decomposeFin'Symm i 1 =
      Equiv.Perm.decomposeFin'Symm (σ i) (cechPermDelete σ i) := by
    ext j
    refine Fin.cases ?_ (fun j ↦ ?_) j
    · simp
    · simp [Equiv.Perm.mul_apply, cechPermDelete_apply]
  simpa using congrArg Equiv.Perm.sign e

end SerrePositivity.AlgebraicGeometry
