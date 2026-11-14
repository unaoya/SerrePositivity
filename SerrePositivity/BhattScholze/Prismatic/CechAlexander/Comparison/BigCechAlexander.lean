module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Comparison.PolynomialCompletionFunctor
public import SerrePositivity.BhattScholze.Prismatic.Envelopes.CompletedFreeDelta
public import SerrePositivity.BhattScholze.Prism.Basic.Rigidity
public import SerrePositivity.HomologicalAlgebra.Cosimplicial.Algebra
public import Mathlib.CategoryTheory.Functor.Currying

/-!
# 大きい prismatic Čech–Alexander 模型の関手性

## 概要
完備多項式代数の全元を添字に取った包から、厳密な余単体的模型を組む。

## 方針
多項式代入を完備化して枠の添字に作用させる。包の普遍性により
余単体の写像および代入から来る射を同時に構成する。

## 規約
各項に未閉包の評価核を使う。包の普遍性は `IsPrismaticEnvelope.of_closure` で
導来 p 完備化を使う閉包の場合にも移る。

## 使われ方
BS 著者版 Construction 4.18 と Theorem 6.4 の大きい枠。
-/

public noncomputable section

open CategoryTheory SerrePositivity.DerivedCompletion

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A)

local notation "C" => (A ⧸ P.ideal)

/-- 大きい枠は完備多項式環の各元を頂点ごとに変数に取る。 -/
abbrev BigCechIndex (Q : Poly C) (n : ℕ) := polyCompletion P Q.n × Fin (n + 1)

variable {P}

/-- 大きい枠の多項式環を完備多項式環へ評価する。 -/
def bigCechEval (Q : Poly C) (n : ℕ) :
    MvPolynomial (BigCechIndex P Q n) A →+* polyCompletion P Q.n :=
  MvPolynomial.eval₂Hom
    ((algebraMap C (polyCompletion P Q.n)).comp (Ideal.Quotient.mk P.ideal)) Prod.fst

variable (P)

/-- 大きい枠の多項式環を完備自由 δ 環へ送る標準射。 -/
def bigCechInitial (Q : Poly C) (n : ℕ) :
    MvPolynomial (BigCechIndex P Q n) A →+* completedFreeDelta P (BigCechIndex P Q n) :=
  (pdCompletionUnit _ p (algebraMap A _ P.generator)).comp
    (relativeFreeInitialPolynomialMap (BigCechIndex P Q n) A).toRingHom

@[simp] theorem bigCechInitial_X (Q : Poly C) (n : ℕ) (s : BigCechIndex P Q n) :
    bigCechInitial P Q n (MvPolynomial.X s) = completedFreeDeltaVariable P _ s := by
  change pdCompletionUnit _ p _ (relativeFreeInitialPolynomialMap _ _ (MvPolynomial.X s)) = _
  rw [relativeFreeInitialPolynomialMap, MvPolynomial.rename_X]
  rfl

@[simp] theorem bigCechInitial_C (Q : Poly C) (n : ℕ) (a : A) :
    bigCechInitial P Q n (MvPolynomial.C a) = completedFreeDeltaBase P _ a := by
  change pdCompletionUnit _ p _ (relativeFreeInitialPolynomialMap _ _ (MvPolynomial.C a)) = _
  rw [relativeFreeInitialPolynomialMap, MvPolynomial.rename_C]
  rfl

/-- 評価核が完備自由 δ 環に生成するイデアル。 -/
def bigCechIdeal (Q : Poly C) (n : ℕ) : Ideal (completedFreeDelta P (BigCechIndex P Q n)) :=
  (RingHom.ker (bigCechEval Q n)).map (bigCechInitial P Q n)

theorem generator_mem_bigCechIdeal (Q : Poly C) (n : ℕ) :
    completedFreeDeltaBase P _ P.generator ∈ bigCechIdeal P Q n := by
  rw [← bigCechInitial_C P Q n]
  apply Ideal.mem_map_of_mem
  change bigCechEval Q n (MvPolynomial.C P.generator) = 0
  rw [bigCechEval, MvPolynomial.eval₂Hom_C]
  change algebraMap C (polyCompletion P Q.n) (Ideal.Quotient.mk P.ideal P.generator) = 0
  have h : Ideal.Quotient.mk P.ideal P.generator = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  rw [h, map_zero]

/-- 大きい枠の次数 n における包のデータ。 -/
structure BigCechTerm (Q : Poly C) (n : ℕ) where
  carrier : Type u
  [ring : CommRing carrier]
  prism : OrientedPrism p carrier
  unit : completedFreeDelta P (BigCechIndex P Q n) →+* carrier
  isEnvelope : IsPrismaticEnvelope P (completedFreeDeltaStructure P _)
    (completedFreeDeltaBase P _) (completedFreeDeltaBase_isDeltaHom P _)
    (bigCechIdeal P Q n) (generator_mem_bigCechIdeal P Q n) prism unit

attribute [instance] BigCechTerm.ring

namespace BigCechTerm

variable {P} {Q Q' Q'' : Poly (A ⧸ P.ideal)} {l m n : ℕ}
variable (E : BigCechTerm P Q l) (F : BigCechTerm P Q' m) (G : BigCechTerm P Q'' n)

/-- 大きい枠の包の基底射。 -/
@[expose] def base : OrientedPrism.Hom P E.prism :=
  ⟨E.unit.comp (completedFreeDeltaBase P _),
    E.isEnvelope.isDeltaHom.comp (completedFreeDeltaBase_isDeltaHom P _),
    E.isEnvelope.base_hom⟩

/-- 指定した頂点の変数の像。 -/
def variableImage (s : BigCechIndex P Q l) : E.carrier :=
  E.unit (completedFreeDeltaVariable P _ s)

variable (f : Q ⟶ Q') (θ : Fin (l + 1) → Fin (m + 1))

/-- 多項式の代入と単体の写像が変数の添字に誘導する写像。 -/
def indexMap (s : BigCechIndex P Q l) : BigCechIndex P Q' m :=
  (polyCompletionMap P f s.1, θ s.2)

private theorem existsUnique_eval :
    ∃! g : completedFreeDelta P (BigCechIndex P Q l) →+* F.carrier,
      (completedFreeDeltaStructure P _).IsDeltaHom F.prism.deltaStructure g ∧
      g.comp (completedFreeDeltaBase P _) = F.base.toRingHom ∧
      ∀ s, g (completedFreeDeltaVariable P _ s) = F.variableImage (indexMap f θ s) :=
  existsUnique_completedFreeDeltaHom P _ F.prism.deltaStructure F.base.toRingHom
    F.base.map_delta F.prism.complete_p F.base.isModuleComplete_map_generator
    (fun s => F.variableImage (indexMap f θ s))

private def eval : completedFreeDelta P (BigCechIndex P Q l) →+* F.carrier :=
  (F.existsUnique_eval f θ).choose

private theorem eval_spec :
    (completedFreeDeltaStructure P _).IsDeltaHom F.prism.deltaStructure (F.eval f θ) ∧
    (F.eval f θ).comp (completedFreeDeltaBase P _) = F.base.toRingHom ∧
    ∀ s, F.eval f θ (completedFreeDeltaVariable P _ s) =
      F.variableImage (indexMap f θ s) :=
  (F.existsUnique_eval f θ).choose_spec.1

private theorem eval_ideal :
    (bigCechIdeal P Q l).map (F.eval f θ) ≤ F.prism.ideal := by
  let ρ := (MvPolynomial.rename (indexMap f θ) :
    MvPolynomial (BigCechIndex P Q l) A →ₐ[A] MvPolynomial (BigCechIndex P Q' m) A).toRingHom
  have he : (F.eval f θ).comp (bigCechInitial P Q l) =
      F.unit.comp ((bigCechInitial P Q' m).comp ρ) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change F.eval f θ (bigCechInitial P Q l (MvPolynomial.C a)) =
        F.unit (bigCechInitial P Q' m (ρ (MvPolynomial.C a)))
      rw [show ρ (MvPolynomial.C a) = MvPolynomial.C a from MvPolynomial.rename_C _ _,
        bigCechInitial_C, bigCechInitial_C]
      exact RingHom.congr_fun (F.eval_spec f θ).2.1 a
    · intro s
      change F.eval f θ (bigCechInitial P Q l (MvPolynomial.X s)) =
        F.unit (bigCechInitial P Q' m (ρ (MvPolynomial.X s)))
      rw [show ρ (MvPolynomial.X s) = MvPolynomial.X (indexMap f θ s)
          from MvPolynomial.rename_X _ _, bigCechInitial_X, bigCechInitial_X]
      exact (F.eval_spec f θ).2.2 s
  have heval : (bigCechEval Q' m).comp ρ =
      (polyCompletionMap P f).toRingHom.comp (bigCechEval Q l) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change bigCechEval Q' m (ρ (MvPolynomial.C a)) =
        polyCompletionMap P f (bigCechEval Q l (MvPolynomial.C a))
      rw [show ρ (MvPolynomial.C a) = MvPolynomial.C a from MvPolynomial.rename_C _ _,
        bigCechEval, bigCechEval, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C]
      exact ((polyCompletionMap P f).commutes _).symm
    · intro s
      change bigCechEval Q' m (ρ (MvPolynomial.X s)) =
        polyCompletionMap P f (bigCechEval Q l (MvPolynomial.X s))
      rw [show ρ (MvPolynomial.X s) = MvPolynomial.X (indexMap f θ s)
        from MvPolynomial.rename_X _ _, bigCechEval, bigCechEval,
        MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']
      rfl
  have hρ : (RingHom.ker (bigCechEval Q l)).map ρ ≤ RingHom.ker (bigCechEval Q' m) := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    change ((bigCechEval Q' m).comp ρ) a = 0
    rw [RingHom.congr_fun heval a, RingHom.comp_apply, RingHom.mem_ker.mp ha, map_zero]
  rw [bigCechIdeal, Ideal.map_map, he, ← Ideal.map_map, ← Ideal.map_map]
  exact (Ideal.map_mono (Ideal.map_mono hρ)).trans F.isEnvelope.map_le

private theorem existsUnique_map :
    ∃! g : E.carrier →+* F.carrier, E.prism.deltaStructure.IsDeltaHom F.prism.deltaStructure g ∧
      g.comp E.unit = F.eval f θ :=
  E.isEnvelope.lift F.prism _ (F.eval_spec f θ).1
    (by rw [(F.eval_spec f θ).2.1]; exact F.base.ideal_le) (F.eval_ideal f θ)

/-- 多項式代入と頂点の写像が誘導する包の環射。 -/
def map : E.carrier →+* F.carrier := (E.existsUnique_map F f θ).choose

theorem map_isDeltaHom :
    E.prism.deltaStructure.IsDeltaHom F.prism.deltaStructure (E.map F f θ) :=
  (E.existsUnique_map F f θ).choose_spec.1.1

theorem map_base : (E.map F f θ).comp E.base.toRingHom = F.base.toRingHom := by
  change (E.map F f θ).comp (E.unit.comp (completedFreeDeltaBase P _)) = _
  have h : (E.map F f θ).comp E.unit = F.eval f θ :=
    (E.existsUnique_map F f θ).choose_spec.1.2
  rw [← RingHom.comp_assoc, h]
  exact (F.eval_spec f θ).2.1

theorem map_variableImage (s : BigCechIndex P Q l) :
    E.map F f θ (E.variableImage s) = F.variableImage (indexMap f θ s) := by
  change ((E.map F f θ).comp E.unit) (completedFreeDeltaVariable P _ s) = _
  have h : (E.map F f θ).comp E.unit = F.eval f θ :=
    (E.existsUnique_map F f θ).choose_spec.1.2
  rw [h]
  exact (F.eval_spec f θ).2.2 s

/-- 包の δ 射は基底と枠の変数上の値で決まる。 -/
theorem map_unique (g : E.carrier →+* F.carrier)
    (hg : E.prism.deltaStructure.IsDeltaHom F.prism.deltaStructure g)
    (hb : g.comp E.base.toRingHom = F.base.toRingHom)
    (hvar : ∀ s, g (E.variableImage s) = F.variableImage (indexMap f θ s)) :
    g = E.map F f θ := by
  apply (E.existsUnique_map F f θ).choose_spec.2
  refine ⟨hg, ?_⟩
  apply completedFreeDeltaHom_ext P _ F.prism.deltaStructure F.base.toRingHom F.base.map_delta
    F.prism.complete_p F.base.isModuleComplete_map_generator
    (hg.comp E.isEnvelope.isDeltaHom) (F.eval_spec f θ).1
  · rwa [RingHom.comp_assoc]
  · exact (F.eval_spec f θ).2.1
  · intro s
    exact (hvar s).trans ((F.eval_spec f θ).2.2 s).symm

theorem map_id : E.map E (𝟙 Q) id = RingHom.id _ := by
  symm
  apply E.map_unique E (𝟙 Q) id _ (DeltaStructure.isDeltaHom_id _)
  · exact RingHom.id_comp _
  · rintro ⟨s, i⟩
    simp only [indexMap, polyCompletionMap_id, AlgHom.id_apply, id_eq, RingHom.id_apply]

theorem map_comp (g : Q' ⟶ Q'') (τ : Fin (m + 1) → Fin (n + 1)) :
    E.map G (f ≫ g) (τ ∘ θ) = (F.map G g τ).comp (E.map F f θ) := by
  symm
  apply E.map_unique G (f ≫ g) (τ ∘ θ) _
    ((F.map_isDeltaHom G g τ).comp (E.map_isDeltaHom F f θ))
  · rw [RingHom.comp_assoc, E.map_base, F.map_base]
  · intro s
    simp only [RingHom.comp_apply, E.map_variableImage, F.map_variableImage, indexMap,
      polyCompletionMap_comp, AlgHom.comp_apply, Function.comp_apply]

end BigCechTerm

/-- 大きい枠の包の選択から得る、代入と単体の両方で厳密な関手。 -/
def bigCechAlexanderOfTerms (E : ∀ (Q : Poly C) n, BigCechTerm P Q n) :
    Poly C ⥤ SerrePositivity.Cosimplicial.CosimplicialAlgebra A :=
  Functor.curry.obj ({
    obj X := Under.mk (CommRingCat.ofHom (E X.1 X.2.len).base.toRingHom)
    map {X Y} f := Under.homMk (CommRingCat.ofHom
      ((E X.1 X.2.len).map (E Y.1 Y.2.len) f.1 f.2.toOrderHom))
      (CommRingCat.hom_ext ((E X.1 X.2.len).map_base _ _ _))
    map_id X := by
      apply Under.UnderMorphism.ext
      apply CommRingCat.hom_ext
      exact (E X.1 X.2.len).map_id
    map_comp {X Y Z} f g := by
      apply Under.UnderMorphism.ext
      apply CommRingCat.hom_ext
      exact (E X.1 X.2.len).map_comp (E Y.1 Y.2.len) (E Z.1 Z.2.len)
        f.1 f.2.toOrderHom g.1 g.2.toOrderHom
    } : Poly C × SimplexCategory ⥤ Under (CommRingCat.of A))

end SerrePositivity.BhattScholze.Prismatic

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Construction 4.18" (partial := component) "大きい枠の Čech–Alexander 模型の項と座標変換（BS-D69 P2）。Δ を計算することは G9・G10 待ち ／ 11-11 更新 ／ 11-12 夜更新（§4 の見直し）"] _root_.SerrePositivity.BhattScholze.Prismatic.bigCechEval
