module
public import SerrePositivity.DifferentialGraded.Complexes.HomComplex
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Logic.Small.Basic

/-! # 非有界複体の直和の部分族と分裂写像

## 概要
非有界複体の直和の部分族と分裂写像。

## 方針
既存の全dg自然なHom・作用・chain mapと局所化の計算を再利用する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。dg加群の導来作用・準同値比較の基盤。任意可換環上のMorita・K理論のモデル比較に再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded.ComplexCoproduct
open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A] {J : Type v} [Small.{u} J]
variable (K : J → Complex A)

lemma cochain_ext {T : Complex A} (p : ℤ) (f g : Cochain (∐ K) T p)
    (h : ∀ j, (Cochain.ofHom (Sigma.ι K j)).comp f (zero_add p) =
      (Cochain.ofHom (Sigma.ι K j)).comp g (zero_add p)) : f = g := by
  apply Cochain.ext
  intro i n hn
  apply (isColimitOfPreserves (HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) i)
    (colimit.isColimit (Discrete.functor K))).hom_ext
  intro j
  change (Sigma.ι K j.as).f i ≫ f.v i n hn = (Sigma.ι K j.as).f i ≫ g.v i n hn
  simpa only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v] using
    congrArg (fun z : Cochain (K j.as) T p => z.v i n hn) (h j.as)

def cochainDesc (T : Complex A) (p : ℤ) (f : ∀ j, Cochain (K j) T p) :
    Cochain (∐ K) T p :=
  Cochain.mk (fun i n hn =>
    (isColimitOfHasCoproductOfPreservesColimit
      (HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) i) K).desc
      (Cofan.mk (T.X n) (fun j => (f j).v i n hn)))

lemma cochainDesc_precomp (T : Complex A) (p : ℤ) (f : ∀ j, Cochain (K j) T p) (j : J) :
    (Cochain.ofHom (Sigma.ι K j)).comp (cochainDesc K T p f) (zero_add p) = f j := by
  apply Cochain.ext
  intro i n hn
  rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, cochainDesc, Cochain.mk_v]
  exact (isColimitOfHasCoproductOfPreservesColimit
    (HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) i) K).fac
    (Cofan.mk (T.X n) (fun j => (f j).v i n hn)) ⟨j⟩

abbrev subfamily (S : Set J) : Complex A := ∐ (fun j : S => K j.val)

def inclusion (S : Set J) : subfamily K S ⟶ ∐ K :=
  Sigma.desc (fun j : S => Sigma.ι K j.val)

lemma ι_inclusion (S : Set J) (j : S) :
    Sigma.ι (fun j : S => K j.val) j ≫ inclusion K S = Sigma.ι K j.val :=
  Sigma.ι_comp_desc _ _

def projection (S : Set J) : ∐ K ⟶ subfamily K S := by
  classical
  exact Sigma.desc (fun j => if h : j ∈ S then Sigma.ι (fun j : S => K j.val) ⟨j, h⟩ else 0)

lemma ι_projection_mem (S : Set J) (j : J) (hj : j ∈ S) :
    Sigma.ι K j ≫ projection K S = Sigma.ι (fun j : S => K j.val) ⟨j, hj⟩ := by
  classical
  simp only [projection, Sigma.ι_comp_desc, dite_eq_left hj]

lemma ι_projection_not_mem (S : Set J) (j : J) (hj : j ∉ S) :
    Sigma.ι K j ≫ projection K S = 0 := by
  classical
  simp only [projection, Sigma.ι_comp_desc, dite_eq_right hj]

lemma inclusion_projection (S : Set J) : inclusion K S ≫ projection K S = 𝟙 _ := by
  apply Sigma.hom_ext
  intro j
  rw [← Category.assoc, ι_inclusion, ι_projection_mem K S j.val j.property, Category.comp_id]

instance inclusion_splitMono (S : Set J) : IsSplitMono (inclusion K S) :=
  ⟨⟨{ retraction := projection K S, id := inclusion_projection K S }⟩⟩

/-- 部分族間の成分選択。包含関係はこの写像の定義には不要。 -/
def select (S T : Set J) : subfamily K S ⟶ subfamily K T :=
  inclusion K S ≫ projection K T

lemma ι_select_mem (S T : Set J) (j : S) (hj : j.val ∈ T) :
    Sigma.ι (fun j : S => K j.val) j ≫ select K S T =
      Sigma.ι (fun j : T => K j.val) ⟨j.val, hj⟩ := by
  rw [select, ← Category.assoc, ι_inclusion, ι_projection_mem]

lemma ι_select_not_mem (S T : Set J) (j : S) (hj : j.val ∉ T) :
    Sigma.ι (fun j : S => K j.val) j ≫ select K S T = 0 := by
  rw [select, ← Category.assoc, ι_inclusion, ι_projection_not_mem K T j.val hj]

lemma select_self (S : Set J) : select K S S = 𝟙 _ := inclusion_projection K S

lemma select_inclusion (S T : Set J) (h : S ⊆ T) :
    select K S T ≫ inclusion K T = inclusion K S := by
  apply Sigma.hom_ext
  intro j
  rw [← Category.assoc, ι_select_mem K S T j (h j.property), ι_inclusion, ι_inclusion]

lemma select_comp (S T U : Set J) (h : S ⊆ T) :
    select K S T ≫ select K T U = select K S U := by
  change select K S T ≫ (inclusion K T ≫ projection K U) = _
  rw [← Category.assoc, select_inclusion K S T h]
  rfl

lemma select_zero (S T : Set J) (h : Disjoint S T) : select K S T = 0 := by
  apply Sigma.hom_ext
  intro j
  rw [ι_select_not_mem K S T j (fun hj => Set.disjoint_left.mp h j.property hj),
    Limits.comp_zero]

/-- 互いに素な二部分族から、上位の部分族の恒等射を分解する。 -/
lemma select_partition (S T U : Set J) (hS : S ⊆ U) (hT : T ⊆ U)
    (hST : Disjoint S T) (hU : U ⊆ S ∪ T) :
    select K U S ≫ select K S U + select K U T ≫ select K T U = 𝟙 _ := by
  classical
  apply Sigma.hom_ext
  intro j
  rw [Preadditive.comp_add, ← Category.assoc, ← Category.assoc, Category.comp_id]
  rcases hU j.property with hj | hj
  · rw [ι_select_mem K U S j hj,
      ι_select_mem K S U ⟨j.val, hj⟩ (hS hj),
      ι_select_not_mem K U T j (fun ht => Set.disjoint_left.mp hST hj ht),
      Limits.zero_comp, add_zero]
  · rw [ι_select_not_mem K U S j (fun hs => Set.disjoint_left.mp hST hs hj),
      Limits.zero_comp, zero_add, ι_select_mem K U T j hj,
      ι_select_mem K T U ⟨j.val, hj⟩ (hT hj)]

end SerrePositivity.DifferentialGraded.ComplexCoproduct
