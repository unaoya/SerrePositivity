module

public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.PowerRootPolynomial
public import SerrePositivity.BhattScholze.Andre.Transfinite.Colimit
public import SerrePositivity.BhattScholze.Perfectoidization.Derived.Interface
public import SerrePositivity.CommutativeAlgebra.Perfectoid.Torsion
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# 完備な可換環への根添加

## 概要
全元に mod p で p 乗根を添加する完備な一段と可算塔、完備化前の代数的な根添加、
有限変数の両立する根の環と完備な底変換を構成する。完備な根添加と代数的な根添加は関手的である。

## 方針
多項式環の商の普遍性、逐次余極限、導来完備化 H⁰ の普遍性を用いる。
有限変数の根の環の perfectoid 性は、単項式表示と distinguished 係数商から示す。

## 規約
入力は通常の可換環。完備化は導来 p 完備化の H⁰ を取る。

## 使われ方
BS 著者版 Proposition 8.5 の証明の弱始対象と被覆の構成、Lemma 8.8 の前段に使う。
-/

@[expose] public noncomputable section

universe u

open CategoryTheory

namespace SerrePositivity.BhattScholze.Perfectoidization.Derived

open SerrePositivity.BhattScholze.PerfectoidizationInterface

variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] (hR : IsIntegralPerfectoid R p)
variable (S : Type u) [CommRing S] [Algebra R S]

/-! ## (1) S̃（弱始対象の土台） -/

/-- 各 a に対する a − X_a^p − pY_a で生成される一段の関係イデアル。 -/
def algebraicStepIdeal (C : CommRingCat.{u}) : Ideal (MvPolynomial (C ⊕ C) C) :=
  Ideal.span (Set.range fun a : C => MvPolynomial.C a -
    MvPolynomial.X (Sum.inl a) ^ p - (p : MvPolynomial (C ⊕ C) C) * MvPolynomial.X (Sum.inr a))

/-- 概要：一段：S_1 = (S⟨X_s, Y_s : s ∈ S⟩/(s − X_s^p − pY_s))^∧（全元に p 乗根を mod p で添加）。
方針：`MvPolynomial (S ⊕ S) S` を関係 `s − X_s^p − p·Y_s` で割り、p 進完備化（`PrincipalCompletionH0 _ p` の H⁰、U4）。
規約：関手的（S の射で変数を送る）。
使われ方：`rootClosure`。 -/
abbrev rootAdjunctionStep (p : ℕ) (R S : Type u) [CommRing R] [CommRing S] :=
  ↥(completionRing p (CommRingCat.of
    (MvPolynomial (S ⊕ S) S ⧸ algebraicStepIdeal p (CommRingCat.of S))))

/-- 係数の包含を商と導来完備化へ送る。 -/
def rootAdjunctionStepUnit : S →+* rootAdjunctionStep p R S :=
  (completionUnit p _).hom.comp ((Ideal.Quotient.mk (algebraicStepIdeal p _)).comp MvPolynomial.C)

instance : Algebra R (rootAdjunctionStep p R S) :=
  ((rootAdjunctionStepUnit p R S).comp (algebraMap R S)).toAlgebra

/-- 概要：perfectoid 環 T への環射 S → T は、一段の根添加を通る。
方針：各元の像 t について t − y^p = pz を満たす y, z を選び、多項式環の普遍性と
導来完備化の普遍性を使う。
規約：延長は一意でない。
使われ方：`rootClosure_extends`。 -/
theorem rootAdjunctionStep_extends (T : Type u) [CommRing T]
    (hT : IsIntegralPerfectoid T p) (g : S →+* T) :
    ∃ l : rootAdjunctionStep p R S →+* T, l.comp (rootAdjunctionStepUnit p R S) = g := by
  classical
  let I : Ideal T := Ideal.span {(p : T)}
  let q : T →+* T ⧸ I := Ideal.Quotient.mk I
  have hfrob : Function.Surjective (fun x : T ⧸ I => x ^ p) := by
    rcases hT with hT | ⟨_, _, _, hfrob, _⟩
    · let := hT
      let : Subsingleton (T ⧸ I) := q.codomain_trivial
      exact fun _ => ⟨0, Subsingleton.elim _ _⟩
    · exact hfrob
  have hroots (a : S) : ∃ y z : T, g a - y ^ p = (p : T) * z := by
    obtain ⟨b, hb⟩ := hfrob (q (g a))
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective b
    have hmem : g a - y ^ p ∈ I := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [map_sub, map_pow]
      exact sub_eq_zero.mpr hb.symm
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.mp hmem
    exact ⟨y, z, hz⟩
  choose y z hz using hroots
  let eval : MvPolynomial (S ⊕ S) S →+* T := MvPolynomial.eval₂Hom g (Sum.elim y z)
  have hker : algebraicStepIdeal p (CommRingCat.of S) ≤ RingHom.ker eval := by
    apply Ideal.span_le.mpr
    rintro _ ⟨a, rfl⟩
    change eval _ = 0
    simp only [eval, map_sub, map_pow, map_mul, map_natCast, MvPolynomial.eval₂Hom_C,
      MvPolynomial.eval₂Hom_X', Sum.elim_inl, Sum.elim_inr]
    rw [hz a, sub_self]
  let evalQuot := Ideal.Quotient.lift (algebraicStepIdeal p (CommRingCat.of S)) eval hker
  let f := CommRingCat.ofHom evalQuot
  let l := completionLift p f (hT.isModuleComplete T p)
  refine ⟨l.hom, ?_⟩
  ext x
  change (completionUnit p _ ≫ l).hom (Ideal.Quotient.mk _ (MvPolynomial.C x)) = g x
  rw [completionLift_comp]
  exact MvPolynomial.eval₂Hom_C g (Sum.elim y z) x

/-- 概要：S̃ := (colim_k S_k)^∧（ω 段、D51）。
方針：段の余極限（通常の環の sequential 余極限）の p 進完備化。
規約：R 代数、S → S̃。
使われ方：弱始対象（A5-4）、A6-1（Lemma 8.8 の R₀ 上の根添加）。 -/
def completedStages : ℕ → CommRingCat.{u}
  | 0 => CommRingCat.of S
  | n + 1 => CommRingCat.of (rootAdjunctionStep p R (completedStages n))

/-- 各完備な根添加の単位を後続射とする逐次図式。 -/
def completedRootTower : ℕ ⥤ CommRingCat.{u} :=
  Functor.ofSequence (X := completedStages p R S) fun n =>
    CommRingCat.ofHom (rootAdjunctionStepUnit p R ((completedStages p R S) n))

/-- 完備な根添加の逐次余極限の導来 p 完備化 H⁰。 -/
abbrev rootClosure := ↥(completionRing p (Limits.colimit (completedRootTower p R S)))

/-- 第零段を余極限に送り、導来完備化の単位と合成する。 -/
def rootClosureUnit : S →+* rootClosure p R S :=
  (completionUnit p _).hom.comp (Limits.colimit.ι (completedRootTower p R S) 0).hom

instance : Algebra R (rootClosure p R S) :=
  ((rootClosureUnit p R S).comp (algebraMap R S)).toAlgebra

/-- 概要：S̃ は p 進完備（完備化なので）。
方針：`PrincipalCompletionH0` の完備性（既存 `principalCompletionH0_isCompleteModuleReflection`）。
規約：`IsModuleComplete`（HA/DerivedCompletion/Module）。
使われ方：κ 側の site の対象であること、Cor 8.12 の前提。 -/
theorem rootClosure_isModuleComplete :
    SerrePositivity.DerivedCompletion.IsModuleComplete (rootClosure p R S)
      (p : rootClosure p R S) (ModuleCat.of (rootClosure p R S) (rootClosure p R S)) := by
  exact completionRing_complete p _

/-- 概要：perfectoid 環 T への環射 S → T は、完備な根添加の余極限 S̃ を通る。
方針：各後続段に延長し、余極限と完備化の普遍性を使う。
規約：延長の存在を述べる。標的は perfectoid。
使われ方：弱始性、A6 の `exists_perfectoid_arcCover`。 -/
theorem rootClosure_extends (T : Type u) [CommRing T]
    (hT : IsIntegralPerfectoid T p) (g : S →+* T) :
    ∃ l : rootClosure p R S →+* T, l.comp (rootClosureUnit p R S) = g := by
  classical
  let F := completedRootTower p R S
  let T' := CommRingCat.of T
  have step (n : ℕ) (f : F.obj n ⟶ T') :
      ∃ l : F.obj (n + 1) →+* T, l.comp (rootAdjunctionStepUnit p R (F.obj n)) = f.hom := by
    letI : Algebra R (F.obj n) :=
      ((F.map (homOfLE (Nat.zero_le n))).hom.comp (algebraMap R S)).toAlgebra
    exact rootAdjunctionStep_extends p R (F.obj n) T hT f.hom
  let lift : ∀ n : ℕ, F.obj n ⟶ T' :=
    Nat.rec (CommRingCat.ofHom g) (fun n f => CommRingCat.ofHom (step n f).choose)
  let cocone : Limits.Cocone F :=
    { pt := T'
      ι := NatTrans.ofSequence lift (fun n => by
        change (completedRootTower p R S).map (homOfLE (Nat.le_add_right n 1)) ≫ lift (n + 1) =
          lift n ≫ 𝟙 T'
        have hmap : F.map (homOfLE (Nat.le_add_right n 1)) =
            CommRingCat.ofHom (rootAdjunctionStepUnit p R (F.obj n)) :=
          Functor.ofSequence_map_homOfLE_succ _ n
        rw [Category.comp_id, hmap]
        apply CommRingCat.hom_ext
        exact (step n (lift n)).choose_spec) }
  let d := Limits.colimit.desc F cocone
  let l := completionLift p d (hT.isModuleComplete T p)
  refine ⟨l.hom, ?_⟩
  have h : Limits.colimit.ι F 0 ≫ completionUnit p (Limits.colimit F) ≫ l =
      CommRingCat.ofHom g := by
    rw [completionLift_comp, Limits.colimit.ι_desc]
    rfl
  exact congrArg (fun f : CommRingCat.of S ⟶ T' => f.hom) h

/-! ## (2) 完備化前の代数的な根添加 -/

/-- 概要：完備化前の代数的根添加の各段。第零段は C。
方針：各後続段で、全元 a について a − X_a^p − pY_a を関係とする多項式環の商を取る。
規約：通常の環。
使われ方：`algebraicRootClosure` の逐次余極限。 -/
def algebraicStages (C : CommRingCat.{u}) : ℕ → CommRingCat.{u}
  | 0 => C
  | n + 1 =>
    let B := algebraicStages C n
    CommRingCat.of (MvPolynomial (B ⊕ B) B ⧸ algebraicStepIdeal p B)

/-- 根添加の係数包含を後続射とする、完備化前の逐次図式。 -/
def algebraicTower (C : CommRingCat.{u}) : ℕ ⥤ CommRingCat.{u} :=
  Functor.ofSequence (X := algebraicStages p C) fun _n =>
    CommRingCat.ofHom ((Ideal.Quotient.mk (algebraicStepIdeal p _)).comp MvPolynomial.C)

/-- 完備化前の代数的な根添加の逐次余極限。 -/
abbrev algebraicRootClosure (C : Type u) [CommRing C] :=
  ↥(Limits.colimit (algebraicTower p (CommRingCat.of C)))

/-- 代数的な根添加の逐次余極限への第零段の射。 -/
def algebraicRootClosureUnit (C : Type u) [CommRing C] : C →+* algebraicRootClosure p C :=
  (Limits.colimit.ι (algebraicTower p (CommRingCat.of C)) 0).hom

/-- 完備化前の一段の根添加の環。 -/
abbrev AlgebraicRootStep (p : ℕ) (C : CommRingCat.{u}) :=
  MvPolynomial (C ⊕ C) C ⧸ algebraicStepIdeal p C

/-- 係数と変数を同じ環射で送る、一段の根添加の写像。 -/
def algebraicStepMap {C C' : CommRingCat.{u}} (f : C ⟶ C') :
    AlgebraicRootStep p C →+* AlgebraicRootStep p C' := by
  let rename : MvPolynomial (C ⊕ C) C →+* MvPolynomial (C' ⊕ C') C' :=
    MvPolynomial.eval₂Hom (MvPolynomial.C.comp f.hom)
      (fun j => MvPolynomial.X (Sum.map f.hom f.hom j))
  refine Ideal.quotientMap (algebraicStepIdeal p C') rename ?_
  apply Ideal.span_le.mpr
  rintro _ ⟨a, rfl⟩
  change rename (MvPolynomial.C a - MvPolynomial.X (Sum.inl a) ^ p -
      (p : MvPolynomial (C ⊕ C) C) * MvPolynomial.X (Sum.inr a)) ∈ algebraicStepIdeal p C'
  rw [map_sub, map_sub, map_pow, map_mul, map_natCast]
  dsimp only [rename]
  rw [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']
  exact Ideal.subset_span ⟨f.hom a, rfl⟩

@[simp] private theorem algebraicStepMap_coeff {C C' : CommRingCat.{u}} (f : C ⟶ C') (a : C) :
    algebraicStepMap p f (Ideal.Quotient.mk (algebraicStepIdeal p C) (MvPolynomial.C a)) =
      Ideal.Quotient.mk (algebraicStepIdeal p C') (MvPolynomial.C (f.hom a)) := by
  unfold algebraicStepMap
  erw [Ideal.quotientMap_mk]
  rw [MvPolynomial.eval₂Hom_C]
  rfl

@[simp] private theorem algebraicStepMap_var {C C' : CommRingCat.{u}} (f : C ⟶ C') (j : C ⊕ C) :
    algebraicStepMap p f (Ideal.Quotient.mk (algebraicStepIdeal p C) (MvPolynomial.X j)) =
      Ideal.Quotient.mk (algebraicStepIdeal p C')
        (MvPolynomial.X (Sum.map f.hom f.hom j)) := by
  unfold algebraicStepMap
  erw [Ideal.quotientMap_mk]
  rw [MvPolynomial.eval₂Hom_X']

@[simp] private theorem algebraicStepMap_id (C : CommRingCat.{u}) :
    algebraicStepMap p (𝟙 C) = RingHom.id (AlgebraicRootStep p C) := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro a
    simp
  · intro j
    cases j <;> simp

private theorem algebraicStepMap_comp {C C' C'' : CommRingCat.{u}} (f : C ⟶ C') (g : C' ⟶ C'') :
    algebraicStepMap p (f ≫ g) = (algebraicStepMap p g).comp (algebraicStepMap p f) := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro a
    simp
  · intro j
    cases j <;> simp

/-- 係数と変数の添字を同じ環射で送り、各段の関係を保つ。 -/
def algebraicStageMap {C C' : CommRingCat.{u}} (f : C ⟶ C') :
    ∀ n, algebraicStages p C n ⟶ algebraicStages p C' n
  | 0 => f
  | n + 1 => CommRingCat.ofHom (algebraicStepMap p (algebraicStageMap f n))

private theorem algebraicStageMap_id (C : CommRingCat.{u}) (n : ℕ) :
    algebraicStageMap p (𝟙 C) n = 𝟙 _ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [algebraicStageMap]
    apply CommRingCat.hom_ext
    change algebraicStepMap p (algebraicStageMap p (𝟙 C) n) = RingHom.id _
    rw [ih, algebraicStepMap_id]

private theorem algebraicStageMap_comp {C C' C'' : CommRingCat.{u}}
    (f : C ⟶ C') (g : C' ⟶ C'') (n : ℕ) :
    algebraicStageMap p (f ≫ g) n = algebraicStageMap p f n ≫ algebraicStageMap p g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [algebraicStageMap]
    apply CommRingCat.hom_ext
    change algebraicStepMap p (algebraicStageMap p (f ≫ g) n) =
      (algebraicStepMap p (algebraicStageMap p g n)).comp
        (algebraicStepMap p (algebraicStageMap p f n))
    rw [ih, algebraicStepMap_comp]

private theorem algebraicTower_succ (C : CommRingCat.{u}) (n : ℕ) :
    (algebraicTower p C).map (homOfLE (Nat.le_add_right n 1)) =
      CommRingCat.ofHom
        ((Ideal.Quotient.mk (algebraicStepIdeal p (algebraicStages p C n))).comp
          MvPolynomial.C) :=
  Functor.ofSequence_map_homOfLE_succ _ n

private theorem algebraicStageMap_succ {C C' : CommRingCat.{u}} (f : C ⟶ C') (n : ℕ) :
    algebraicStageMap p f (n + 1) =
      CommRingCat.ofHom (algebraicStepMap p (algebraicStageMap p f n)) := by
  rw [algebraicStageMap]

private theorem algebraicStageMap_naturality {C C' : CommRingCat.{u}} (f : C ⟶ C') (n : ℕ) :
    (algebraicTower p C).map (homOfLE (Nat.le_add_right n 1)) ≫
      algebraicStageMap p f (n + 1) =
    algebraicStageMap p f n ≫ (algebraicTower p C').map (homOfLE (Nat.le_add_right n 1)) := by
  rw [algebraicTower_succ p C n, algebraicTower_succ p C' n, algebraicStageMap_succ]
  apply CommRingCat.hom_ext
  exact RingHom.ext (algebraicStepMap_coeff p (algebraicStageMap p f n))

/-- 段ごとの再添字付けは、係数の包含に沿う後続射と可換。 -/
def algebraicTowerMap {C C' : CommRingCat.{u}} (f : C ⟶ C') :
    algebraicTower p C ⟶ algebraicTower p C' :=
  NatTrans.ofSequence (F := algebraicTower p C) (G := algebraicTower p C')
    (algebraicStageMap p f) (by exact algebraicStageMap_naturality p f)

/-- 代数的根添加の余極限へ段ごとの射を送る。 -/
def algebraicRootClosureMap {C C' : Type u} [CommRing C] [CommRing C'] (f : C →+* C') :
    algebraicRootClosure p C →+* algebraicRootClosure p C' :=
  (Limits.colim.map (algebraicTowerMap p (CommRingCat.ofHom f))).hom

/-- 完備化前の代数的根添加は可換環の関手をなす。 -/
def algebraicRootFunctor : CommRingCat.{u} ⥤ CommRingCat.{u} where
  obj C := Limits.colimit (algebraicTower p C)
  map f := Limits.colim.map (algebraicTowerMap p f)
  map_id C := by
    have h : algebraicTowerMap p (𝟙 C) = 𝟙 _ := by
      apply NatTrans.ext
      funext n
      change algebraicStageMap p (𝟙 C) n = 𝟙 _
      exact algebraicStageMap_id p C n
    rw [h, CategoryTheory.Functor.map_id]
    rfl
  map_comp f g := by
    have h : algebraicTowerMap p (f ≫ g) = algebraicTowerMap p f ≫ algebraicTowerMap p g := by
      apply NatTrans.ext
      funext n
      change algebraicStageMap p (f ≫ g) n = algebraicStageMap p f n ≫ algebraicStageMap p g n
      exact algebraicStageMap_comp p f g n
    rw [h, CategoryTheory.Functor.map_comp]

/-- 一段の代数的な根添加の写像を導来 p 完備化に送る。 -/
def completedStepMap {C C' : CommRingCat.{u}} (f : C ⟶ C') :
    completionRing p (CommRingCat.of (AlgebraicRootStep p C)) ⟶
      completionRing p (CommRingCat.of (AlgebraicRootStep p C')) :=
  completionMap p (CommRingCat.ofHom (algebraicStepMap p f))

private theorem completedStepMap_id (C : CommRingCat.{u}) :
    completedStepMap p (𝟙 C) = 𝟙 _ := by
  have h : CommRingCat.ofHom (algebraicStepMap p (𝟙 C)) =
      𝟙 (CommRingCat.of (AlgebraicRootStep p C)) :=
    CommRingCat.hom_ext (algebraicStepMap_id p C)
  rw [completedStepMap, h, completionMap_id]

private theorem completedStepMap_comp {C C' C'' : CommRingCat.{u}} (f : C ⟶ C') (g : C' ⟶ C'') :
    completedStepMap p (f ≫ g) = completedStepMap p f ≫ completedStepMap p g := by
  have h : CommRingCat.ofHom (algebraicStepMap p (f ≫ g)) =
      CommRingCat.ofHom (algebraicStepMap p f) ≫ CommRingCat.ofHom (algebraicStepMap p g) :=
    CommRingCat.hom_ext (algebraicStepMap_comp p f g)
  simp only [completedStepMap, h, completionMap_comp_map]

private theorem completedStepMap_comp_unit {C C' : CommRingCat.{u}} (f : C ⟶ C') :
    CommRingCat.ofHom (rootAdjunctionStepUnit p R C) ≫ completedStepMap p f =
      f ≫ CommRingCat.ofHom (rootAdjunctionStepUnit p R C') := by
  let j (A : CommRingCat.{u}) : A ⟶ CommRingCat.of (AlgebraicRootStep p A) :=
    CommRingCat.ofHom ((Ideal.Quotient.mk (algebraicStepIdeal p A)).comp MvPolynomial.C)
  let k := CommRingCat.ofHom (algebraicStepMap p f)
  have hj : j C ≫ k = f ≫ j C' :=
    CommRingCat.hom_ext (RingHom.ext (algebraicStepMap_coeff p f))
  change (j C ≫ completionUnit p _) ≫ completionMap p k =
    f ≫ j C' ≫ completionUnit p _
  rw [Category.assoc, completionMap_comp, ← Category.assoc, hj, Category.assoc]

/-- 各完備段で変数を再添字付けし、導来完備化の写像を取る。 -/
def completedStageMap {S' : Type u} [CommRing S'] (f : S →+* S') :
    ∀ n, completedStages p R S n ⟶ completedStages p R S' n
  | 0 => CommRingCat.ofHom f
  | n + 1 => completedStepMap p (completedStageMap f n)

private theorem completedStageMap_id (n : ℕ) :
    completedStageMap p R S (RingHom.id S) n = 𝟙 _ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [completedStageMap, ih, completedStepMap_id] <;> rfl

private theorem completedStageMap_comp {S' S'' : Type u} [CommRing S'] [CommRing S'']
    (f : S →+* S') (g : S' →+* S'') (n : ℕ) :
    completedStageMap p R S (g.comp f) n =
      completedStageMap p R S f n ≫ completedStageMap p R S' g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [completedStageMap, ih, completedStepMap_comp] <;> rfl

omit [Fact p.Prime] [Algebra R S] in
private theorem completedRootTower_succ (n : ℕ) :
    (completedRootTower p R S).map (homOfLE (Nat.le_add_right n 1)) =
      CommRingCat.ofHom (rootAdjunctionStepUnit p R (completedStages p R S n)) :=
  Functor.ofSequence_map_homOfLE_succ _ n

/-- 完備な根添加の各段の写像は後続射と可換。 -/
def completedRootTowerMap {S' : Type u} [CommRing S'] (f : S →+* S') :
    completedRootTower p R S ⟶ completedRootTower p R S' :=
  NatTrans.ofSequence (F := completedRootTower p R S) (G := completedRootTower p R S')
    (completedStageMap p R S f) (by
      intro n
      rw [completedRootTower_succ p R S n, completedRootTower_succ p R S' n, completedStageMap]
      exact completedStepMap_comp_unit p R (completedStageMap p R S f n))

/-- 完備根添加の余極限の写像を、さらに導来完備化へ送る。 -/
def rootClosureMap {S' : Type u} [CommRing S'] [Algebra R S'] (f : S →+* S') :
    rootClosure p R S →+* rootClosure p R S' :=
  (completionMap p (Limits.colim.map (completedRootTowerMap p R S f))).hom

/-- 完備根添加の写像は第零段の単位と可換。 -/
theorem rootClosureMap_comp_unit {S' : Type u} [CommRing S'] [Algebra R S'] (f : S →+* S') :
    (rootClosureMap p R S f).comp (rootClosureUnit p R S) =
      (rootClosureUnit p R S').comp f := by
  let k := completedRootTowerMap p R S f
  have h : Limits.colimit.ι (completedRootTower p R S) 0 ≫ completionUnit p _ ≫
      completionMap p (Limits.colim.map k) =
      CommRingCat.ofHom f ≫ Limits.colimit.ι (completedRootTower p R S') 0 ≫
        completionUnit p _ := by
    have hι : Limits.colimit.ι (completedRootTower p R S) 0 ≫ Limits.colim.map k =
        CommRingCat.ofHom f ≫ Limits.colimit.ι (completedRootTower p R S') 0 :=
      Limits.ι_colimMap k 0
    rw [completionMap_comp, ← Category.assoc, hι]
    exact Category.assoc _ _ _
  exact congrArg (fun g : CommRingCat.of S ⟶ _ => g.hom) h

/-- 完備根添加の写像は恒等射を保つ。 -/
theorem rootClosureMap_id : rootClosureMap p R S (RingHom.id S) = RingHom.id _ := by
  have h : completedRootTowerMap p R S (RingHom.id S) = 𝟙 _ := by
    apply NatTrans.ext
    funext n
    exact completedStageMap_id p R S n
  rw [rootClosureMap, h, CategoryTheory.Functor.map_id, completionMap_id]
  rfl

/-- 完備根添加の写像は環射の合成を保つ。 -/
theorem rootClosureMap_comp {S' S'' : Type u} [CommRing S'] [Algebra R S']
    [CommRing S''] [Algebra R S''] (f : S →+* S') (g : S' →+* S'') :
    rootClosureMap p R S (g.comp f) = (rootClosureMap p R S' g).comp (rootClosureMap p R S f) := by
  have h : completedRootTowerMap p R S (g.comp f) =
      completedRootTowerMap p R S f ≫ completedRootTowerMap p R S' g := by
    apply NatTrans.ext
    funext n
    exact completedStageMap_comp p R S f g n
  simp only [rootClosureMap, h, CategoryTheory.Functor.map_comp, completionMap_comp_map]
  rfl

/-- 概要：代数的な根添加の余極限を mod p に移した環の Frobenius は全射。
方針：元を有限段から取り、次の段で添加した根を余極限と商へ送る。
使われ方：A5-4 の semiperfectoid 被覆への入力。 -/
theorem algebraicRootClosure_frobenius_surjective (C : Type u) [CommRing C] :
    Function.Surjective (fun x : ModP (algebraicRootClosure p C) p ↦ x ^ p) := by
  let F := algebraicTower p (CommRingCat.of C)
  let q : algebraicRootClosure p C →+* ModP (algebraicRootClosure p C) p := Ideal.Quotient.mk _
  intro x
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
  let : Limits.PreservesFilteredColimitsOfSize.{0, 0} (forget CommRingCat.{u}) :=
    Limits.preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  obtain ⟨n, a, ha⟩ := Limits.Concrete.colimit_exists_rep F c
  let qn := Ideal.Quotient.mk (algebraicStepIdeal p (F.obj n))
  let f := q.comp (Limits.colimit.ι F (n + 1)).hom
  refine ⟨f (qn (MvPolynomial.X (Sum.inl a))), ?_⟩
  have he : qn (MvPolynomial.C a - MvPolynomial.X (Sum.inl a) ^ p -
      (p : MvPolynomial (F.obj n ⊕ F.obj n) (F.obj n)) * MvPolynomial.X (Sum.inr a)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨a, rfl⟩)
  have hz : f (qn (MvPolynomial.C a)) - f (qn (MvPolynomial.X (Sum.inl a))) ^ p = 0 := by
    let g := f.comp qn
    have h : g (MvPolynomial.C a - MvPolynomial.X (Sum.inl a) ^ p -
        (p : MvPolynomial (F.obj n ⊕ F.obj n) (F.obj n)) * MvPolynomial.X (Sum.inr a)) = 0 :=
      (congrArg f he).trans (map_zero f)
    have hzero : g (p : MvPolynomial (F.obj n ⊕ F.obj n) (F.obj n)) = 0 := by
      rw [map_natCast, ← map_natCast q]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
    rw [map_sub, map_sub, map_pow, map_mul, hzero, zero_mul, sub_zero] at h
    exact h
  have hmap : F.map (homOfLE (Nat.le_add_right n 1)) = CommRingCat.ofHom
      (qn.comp MvPolynomial.C) := Functor.ofSequence_map_homOfLE_succ _ n
  have hn := Limits.colimit.w F (homOfLE (Nat.le_add_right n 1))
  rw [hmap] at hn
  have hn' := congrArg (fun k : F.obj n ⟶ Limits.colimit F => q (k.hom a)) hn
  exact (sub_eq_zero.mp hz).symm.trans (hn'.trans (congrArg q ha))

/-! ## (3) T_∞ と S ⊗̂_T T_∞ -/

/-- 概要：T = R⟨X_1,…,X_r⟩（p 完備化した多項式環）。
方針：`PrincipalCompletionH0 (MvPolynomial (Fin r) R) p` の H⁰（E3 の `completionRing` と同じ道具、U4）。
規約：R 代数。
使われ方：Lemma 8.6（A5-3）、A5-4 の降下、A1-5。 -/
abbrev polyAlgebra (r : ℕ) := ↥(completionRing p (CommRingCat.of (MvPolynomial (Fin r) R)))
instance (r : ℕ) : Algebra R (polyAlgebra p R r) :=
  ((completionUnit p _).hom.comp MvPolynomial.C).toAlgebra
/-- p 完備化した多項式環における変数の像。 -/
def polyAlgebraVar (r : ℕ) (i : Fin r) : polyAlgebra p R r :=
  (completionUnit p _).hom (MvPolynomial.X i)

/-- 概要：T_∞ = R⟨X_1^{1/p^∞},…,X_r^{1/p^∞}⟩（p 完備化）と T → T_∞。
方針：`MvPolynomial (Fin r × ℕ) R` を `X_{i,n+1}^p − X_{i,n}` で割って p 進完備化する。
規約：変数 `polyRootAlgebraVar i n` は X_i^{1/p^n}。
使われ方：S̃ = S ⊗̂_T T_∞。 -/
def polyRootIdeal (r : ℕ) : Ideal (MvPolynomial (Fin r × ℕ) R) :=
  Ideal.span (Set.range fun j : Fin r × ℕ =>
    MvPolynomial.X (j.1, j.2 + 1) ^ p - MvPolynomial.X j)

section PolynomialMonomials

open SerrePositivity.BhattScholze.Andre
open scoped BigOperators

variable (r : ℕ)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "G" => powerRootExponentMonoid p hp
local notation "Q" => MvPolynomial (Fin r × ℕ) R ⧸ polyRootIdeal p R r
local notation "M" => AddMonoidAlgebra R (Fin r → G)
local notation "q" => Ideal.Quotient.mk (polyRootIdeal p R r)

private abbrev rawRootVar (i : Fin r) (n : ℕ) : Q := q (MvPolynomial.X (i, n))

private theorem rawRootVar_pow (i : Fin r) (n : ℕ) :
    rawRootVar p R r i (n + 1) ^ p = rawRootVar p R r i n := by
  apply sub_eq_zero.mp
  change q (MvPolynomial.X (i, n + 1)) ^ p - q (MvPolynomial.X (i, n)) = 0
  rw [← map_pow, ← map_sub]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨(i, n), rfl⟩)

private def rawRootLift {B : Type u} [CommRing B] (f : R →+* B) (x : Fin r → ℕ → B)
    (hx : ∀ i n, x i (n + 1) ^ p = x i n) : Q →+* B := by
  let ev : MvPolynomial (Fin r × ℕ) R →+* B := MvPolynomial.eval₂Hom f (fun j => x j.1 j.2)
  refine Ideal.Quotient.lift (polyRootIdeal p R r) ev ?_
  change polyRootIdeal p R r ≤ RingHom.ker ev
  apply Ideal.span_le.mpr
  rintro _ ⟨⟨i, n⟩, rfl⟩
  change ev _ = 0
  simp only [ev, map_sub, map_pow, MvPolynomial.eval₂Hom_X', hx, sub_self]

private theorem rawRootLift_coeff {B : Type u} [CommRing B] (f : R →+* B) (x : Fin r → ℕ → B)
    (hx : ∀ i n, x i (n + 1) ^ p = x i n) (a : R) :
    rawRootLift p R r f x hx (q (MvPolynomial.C a)) = f a := by
  unfold rawRootLift
  erw [Ideal.Quotient.lift_mk, MvPolynomial.eval₂Hom_C]

private theorem rawRootLift_var {B : Type u} [CommRing B] (f : R →+* B) (x : Fin r → ℕ → B)
    (hx : ∀ i n, x i (n + 1) ^ p = x i n) (i : Fin r) (n : ℕ) :
    rawRootLift p R r f x hx (rawRootVar p R r i n) = x i n := by
  unfold rawRootLift
  erw [Ideal.Quotient.lift_mk, MvPolynomial.eval₂Hom_X']

private theorem rawRootHom_ext {B : Type u} [CommRing B] {f g : Q →+* B}
    (hC : ∀ a, f (q (MvPolynomial.C a)) = g (q (MvPolynomial.C a)))
    (hX : ∀ i n, f (rawRootVar p R r i n) = g (rawRootVar p R r i n)) : f = g := by
  apply Ideal.Quotient.ringHom_ext
  exact MvPolynomial.ringHom_ext hC (fun j => hX j.1 j.2)

private def rootMonomial (i : Fin r) (n : ℕ) : M :=
  AddMonoidAlgebra.single (Pi.single i (powerRootVariableExponent p hp n)) 1

private theorem rootMonomial_pow (i : Fin r) (n : ℕ) :
    rootMonomial p R r i (n + 1) ^ p = rootMonomial p R r i n := by
  rw [rootMonomial, rootMonomial, AddMonoidAlgebra.single_pow, one_pow]
  congr 1
  ext j
  by_cases h : j = i
  · subst j
    simp [powerRootVariableExponent_nsmul]
  · simp [Pi.single_eq_of_ne h]

private def rawRootToMonomials : Q →+* M :=
  rawRootLift p R r (algebraMap R M) (rootMonomial p R r) (rootMonomial_pow p R r)

private def rootTupleEval : Multiplicative (Fin r → G) →* Q where
  toFun a := ∏ i, powerRootExponentEvalHom p hp (rawRootVar p R r i)
    (rawRootVar_pow p R r i) (Multiplicative.ofAdd (a.toAdd i))
  map_one' := by
    change (∏ i, powerRootExponentEvalHom p hp (rawRootVar p R r i)
      (rawRootVar_pow p R r i) (1 : Multiplicative G)) = 1
    simp
  map_mul' a b := by
    change (∏ i, powerRootExponentEvalHom p hp (rawRootVar p R r i)
      (rawRootVar_pow p R r i)
      (Multiplicative.ofAdd (a.toAdd i) * Multiplicative.ofAdd (b.toAdd i))) = _
    simp only [map_mul, Finset.prod_mul_distrib]

private def rawRootFromMonomials : M →+* Q :=
  AddMonoidAlgebra.liftNCRingHom ((q).comp MvPolynomial.C) (rootTupleEval p R r)
    (fun _ _ => Commute.all _ _)

private theorem rawRootFromMonomials_coeff (a : R) :
    rawRootFromMonomials p R r (algebraMap R M a) = q (MvPolynomial.C a) := by
  change AddMonoidAlgebra.liftNCRingHom ((q).comp MvPolynomial.C) (rootTupleEval p R r) _
    (AddMonoidAlgebra.single 0 a) = _
  rw [AddMonoidAlgebra.liftNCRingHom_single]
  change q (MvPolynomial.C a) * rootTupleEval p R r 1 = q (MvPolynomial.C a)
  rw [map_one, mul_one]

private theorem rawRootFromMonomials_var (i : Fin r) (n : ℕ) :
    rawRootFromMonomials p R r (rootMonomial p R r i n) = rawRootVar p R r i n := by
  rw [rawRootFromMonomials, rootMonomial, AddMonoidAlgebra.liftNCRingHom_single, map_one, one_mul]
  let v : Fin r → G := Pi.single i (powerRootVariableExponent p hp n)
  change rootTupleEval p R r (Multiplicative.ofAdd v) = rawRootVar p R r i n
  change (∏ j : Fin r, powerRootExponentEvalHom p hp
    (rawRootVar p R r j) (rawRootVar_pow p R r j) (Multiplicative.ofAdd (v j))) = _
  dsimp only [v]
  rw [Finset.prod_eq_single i]
  · simp only [Pi.single_eq_same, powerRootExponentEvalHom_variable]
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj]
    exact map_one _
  · simp

private theorem rawRootToMonomials_surjective : Function.Surjective (rawRootToMonomials p R r) := by
  classical
  let f := rawRootToMonomials p R r
  let mono := AddMonoidAlgebra.of R (Fin r → G)
  have hcoeff (a : R) : f (q (MvPolynomial.C a)) = algebraMap R M a :=
    rawRootLift_coeff p R r _ _ _ _
  have hvar (i : Fin r) (n : ℕ) : f (rawRootVar p R r i n) =
      mono (Multiplicative.ofAdd (Pi.single i (powerRootVariableExponent p hp n))) :=
    rawRootLift_var p R r _ _ _ _ _
  intro x
  induction x using AddMonoidAlgebra.induction_on with
  | of e =>
    have hcoord (i : Fin r) : ∃ x : Q, f x = mono (Multiplicative.ofAdd (Pi.single i (e i))) := by
      obtain ⟨n, k, hn⟩ := powerRootExponent_exists_nsmul p hp (e i)
      refine ⟨rawRootVar p R r i n ^ k, ?_⟩
      rw [map_pow, hvar, ← map_pow]
      apply congrArg mono
      change Multiplicative.ofAdd (k • (Pi.single i (powerRootVariableExponent p hp n) :
        Fin r → G)) = Multiplicative.ofAdd (Pi.single i (e i) : Fin r → G)
      rw [hn, Pi.single_nsmul]
    choose a ha using hcoord
    refine ⟨∏ i, a i, ?_⟩
    rw [map_prod]
    calc
      (∏ i, f (a i)) = ∏ i, mono (Multiplicative.ofAdd (Pi.single i (e i))) :=
        Finset.prod_congr rfl (fun i _ => ha i)
      _ = _ := by
        rw [← map_prod]
        apply congrArg mono
        change Multiplicative.ofAdd (∑ i, Pi.single i (e i)) = Multiplicative.ofAdd e
        exact congrArg Multiplicative.ofAdd (Finset.univ_sum_single e)
  | add x y hx hy =>
    obtain ⟨x', rfl⟩ := hx
    obtain ⟨y', rfl⟩ := hy
    exact ⟨x' + y', map_add f x' y'⟩
  | smul a x hx =>
    obtain ⟨x', rfl⟩ := hx
    exact ⟨q (MvPolynomial.C a) * x', by rw [map_mul, hcoeff, Algebra.smul_def]⟩

private def rawRootMonomialEquiv : Q ≃+* M := by
  refine RingEquiv.ofBijective (rawRootToMonomials p R r)
    ⟨?_, rawRootToMonomials_surjective p R r⟩
  have h : (rawRootFromMonomials p R r).comp (rawRootToMonomials p R r) = RingHom.id Q := by
    apply rawRootHom_ext p R r
    · intro a
      change rawRootFromMonomials p R r
        (rawRootLift p R r _ _ _ (q (MvPolynomial.C a))) = q (MvPolynomial.C a)
      rw [rawRootLift_coeff, rawRootFromMonomials_coeff]
    · intro i n
      change rawRootFromMonomials p R r
        (rawRootLift p R r _ _ _ (rawRootVar p R r i n)) = rawRootVar p R r i n
      rw [rawRootLift_var, rawRootFromMonomials_var]
  have hleft : Function.LeftInverse (rawRootFromMonomials p R r) (rawRootToMonomials p R r) :=
    fun x => RingHom.congr_fun h x
  exact hleft.injective

end PolynomialMonomials

/-- 両立する根の関係で割った多項式環の導来 p 完備化 H⁰。 -/
abbrev polyRootAlgebra (r : ℕ) :=
  ↥(completionRing p (CommRingCat.of (MvPolynomial (Fin r × ℕ) R ⧸ polyRootIdeal p R r)))
instance (r : ℕ) : Algebra R (polyRootAlgebra p R r) :=
  ((completionUnit p _).hom.comp
    ((Ideal.Quotient.mk (polyRootIdeal p R r)).comp MvPolynomial.C)).toAlgebra

/-- i 番目の変数の n 段目の根を表す元。 -/
def polyRootAlgebraVar (r : ℕ) (i : Fin r) (n : ℕ) : polyRootAlgebra p R r :=
  (completionUnit p _).hom (Ideal.Quotient.mk (polyRootIdeal p R r) (MvPolynomial.X (i, n)))

/-- 多項式変数を根の第零段に送る完備環の射。 -/
def polyAlgebraToRoot (r : ℕ) : polyAlgebra p R r →+* polyRootAlgebra p R r :=
  (completionMap p (CommRingCat.ofHom ((Ideal.Quotient.mk (polyRootIdeal p R r)).comp
    (MvPolynomial.rename (fun i : Fin r => (i, 0))).toRingHom))).hom

/-- 添加した各変数の根は p 乗で前の段の元に移る。 -/
theorem polyRootAlgebraVar_pow (r : ℕ) (i : Fin r) (n : ℕ) :
    polyRootAlgebraVar p R r i (n + 1) ^ p = polyRootAlgebraVar p R r i n := by
  let C := CommRingCat.of (MvPolynomial (Fin r × ℕ) R ⧸ polyRootIdeal p R r)
  change (completionUnit p C).hom (rawRootVar p R r i (n + 1)) ^ p =
    (completionUnit p C).hom (rawRootVar p R r i n)
  rw [← map_pow, rawRootVar_pow]

/-- 通常の多項式変数は両立する根の第零段へ移る。 -/
theorem polyAlgebraToRoot_var (r : ℕ) (i : Fin r) :
    polyAlgebraToRoot p R r (polyAlgebraVar p R r i) = polyRootAlgebraVar p R r i 0 := by
  let f := CommRingCat.ofHom ((Ideal.Quotient.mk (polyRootIdeal p R r)).comp
    (MvPolynomial.rename (fun j : Fin r => (j, 0))).toRingHom)
  change (completionUnit p _ ≫ completionMap p f).hom (MvPolynomial.X i) = _
  rw [completionMap_comp]
  change (completionUnit p (CommRingCat.of (MvPolynomial (Fin r × ℕ) R ⧸ polyRootIdeal p R r))).hom
    ((Ideal.Quotient.mk (polyRootIdeal p R r))
    (MvPolynomial.rename (fun j : Fin r => (j, 0)) (MvPolynomial.X i))) = _
  rw [MvPolynomial.rename_X]
  rfl

section PolynomialPerfectoid

open SerrePositivity.BhattScholze.Andre
open SerrePositivity.BhattScholze.Andre.Transfinite
open SerrePositivity.DerivedCompletion

universe v

variable {A : Type u} [CommRing A] {E : Type v} [AddCommMonoid E]

private def monomialFrobenius (D : DeltaStructure p A) (hD : D.IsPerfect) (scale : E ≃+ E) :
    AddMonoidAlgebra A E ≃+* AddMonoidAlgebra A E :=
  (AddMonoidAlgebra.mapRingEquiv E (D.frobeniusEquiv hD)).trans
    (AddMonoidAlgebra.mapDomainRingEquiv A scale)

private theorem monomialFrobenius_single (D : DeltaStructure p A) (hD : D.IsPerfect)
    (scale : E ≃+ E) (e : E) (a : A) :
    monomialFrobenius p D hD scale (AddMonoidAlgebra.single e a) =
      AddMonoidAlgebra.single (scale e) (D.frobeniusLift a) := by
  change AddMonoidAlgebra.mapDomain scale
    (AddMonoidAlgebra.mapRingHom E D.frobeniusLift (AddMonoidAlgebra.single e a)) = _
  rw [AddMonoidAlgebra.mapRingHom_single, AddMonoidAlgebra.mapDomain_single]

private theorem monomialFrobenius_mod_p (D : DeltaStructure p A) (hD : D.IsPerfect)
    (scale : E ≃+ E) (hs : ∀ e, scale e = p • e) (x : AddMonoidAlgebra A E) :
    let q := Ideal.Quotient.mk (Ideal.span {(p : AddMonoidAlgebra A E)})
    q (monomialFrobenius p D hD scale x) = q x ^ p := by
  let B := AddMonoidAlgebra A E
  let q := Ideal.Quotient.mk (Ideal.span {(p : B)})
  have hpQ : (p : B ⧸ Ideal.span {(p : B)}) = 0 := by
    change q (p : B) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  have hc (a : A) :
      q (monomialFrobenius p D hD scale (algebraMap A (AddMonoidAlgebra A E) a)) =
        q (algebraMap A (AddMonoidAlgebra A E) a) ^ p := by
    have h : monomialFrobenius p D hD scale (algebraMap A (AddMonoidAlgebra A E) a) =
        algebraMap A (AddMonoidAlgebra A E) (D.frobeniusLift a) := by
      change monomialFrobenius p D hD scale (AddMonoidAlgebra.single 0 a) =
        AddMonoidAlgebra.single 0 (D.frobeniusLift a)
      rw [monomialFrobenius_single, map_zero]
    rw [h, D.frobeniusLift_apply]
    simp only [map_add, map_mul, map_natCast, map_pow, hpQ, zero_mul, add_zero]
  change q (monomialFrobenius p D hD scale x) = q x ^ p
  induction x using AddMonoidAlgebra.induction_on with
  | of e =>
    change q (monomialFrobenius p D hD scale (AddMonoidAlgebra.single e 1)) =
      q (AddMonoidAlgebra.single e 1) ^ p
    rw [monomialFrobenius_single, hs, map_one, ← map_pow, AddMonoidAlgebra.single_pow, one_pow]
  | add x y hx hy =>
    simp only [map_add, hx, hy]
    symm
    simpa only [hpQ, zero_mul, add_zero] using add_pow_prime_eq' (Fact.out : p.Prime) (q x) (q y)
  | smul a x hx =>
    rw [Algebra.smul_def]
    simp only [map_mul, hc, hx, mul_pow]

private theorem exists_perfectMonomialDelta (D : DeltaStructure p A) (hD : D.IsPerfect)
    (scale : E ≃+ E) (hs : ∀ e, scale e = p • e) :
    ∃ D' : DeltaStructure p (AddMonoidAlgebra A E),
      D'.IsPerfect ∧ D.IsDeltaHom D' (algebraMap A (AddMonoidAlgebra A E)) := by
  let B := AddMonoidAlgebra A E
  let : Module.Free A B := Module.Free.of_basis (AddMonoidAlgebra.basis E A)
  have hpB : Function.Injective (fun a : B => (p : B) * a) := by
    simpa only [map_natCast, IsSMulRegular, smul_eq_mul] using
      (show IsSMulRegular A (p : A) from hD.p_mul_injective).of_flat (S := B)
  let φ := monomialFrobenius p D hD scale
  obtain ⟨D', h, _⟩ := DeltaStructure.existsUnique_of_mod_p hpB φ.toRingHom
    (monomialFrobenius_mod_p p D hD scale hs)
  refine ⟨D', ?_, DeltaStructure.isDeltaHom_of_map_frobeniusLift (algebraMap A B) hpB ?_⟩
  · change Function.Bijective D'.frobeniusLift
    rw [h]
    exact φ.bijective
  · intro a
    rw [h]
    symm
    change monomialFrobenius p D hD scale (AddMonoidAlgebra.single 0 a) =
      AddMonoidAlgebra.single 0 (D.frobeniusLift a)
    rw [monomialFrobenius_single, map_zero]

private theorem monomialMap_ker (f : A →+* R) (d : A) (hd : RingHom.ker f = Ideal.span {d}) :
    RingHom.ker (AddMonoidAlgebra.mapRingHom E f) =
      Ideal.span {algebraMap A (AddMonoidAlgebra A E) d} := by
  classical
  let B := AddMonoidAlgebra A E
  let f' := AddMonoidAlgebra.mapRingHom E f
  let J : Ideal B := Ideal.span {algebraMap A B d}
  change RingHom.ker f' = J
  apply le_antisymm
  · intro x hx
    have hz : f' x = 0 := hx
    rw [← AddMonoidAlgebra.sum_coeff_single x]
    apply J.sum_mem
    intro e _
    have he : f (x.coeff e) = 0 := by
      have h := congrArg (fun z : AddMonoidAlgebra R E => z.coeff e) hz
      simpa only [f', AddMonoidAlgebra.coeff_mapRingHom, AddMonoidAlgebra.coeff_zero,
        Finsupp.zero_apply] using h
    have he' : x.coeff e ∈ Ideal.span {d} := hd ▸ (show x.coeff e ∈ RingHom.ker f from he)
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp he'
    rw [ha]
    have hh : AddMonoidAlgebra.single e (d * a) =
        algebraMap A B d * AddMonoidAlgebra.single e a := by
      change AddMonoidAlgebra.single e (d * a) =
        AddMonoidAlgebra.single 0 d * AddMonoidAlgebra.single e a
      rw [AddMonoidAlgebra.single_mul_single, zero_add]
    rw [hh]
    exact J.mul_mem_right _ (Ideal.mem_span_singleton_self _)
  · apply Ideal.span_le.mpr
    rintro _ (rfl : _ = _)
    change f' (algebraMap A B d) = 0
    have h : f d = 0 := show d ∈ RingHom.ker f from hd.symm ▸ Ideal.mem_span_singleton_self d
    change f' (AddMonoidAlgebra.single 0 d) = 0
    simp only [f', AddMonoidAlgebra.mapRingHom_single, h, AddMonoidAlgebra.single_zero]

private theorem monomialBoundedTorsion (hR : IsIntegralPerfectoid R p) :
    ∃ N : ℕ, ∀ n : ℕ, ∀ x : AddMonoidAlgebra R E,
      (p : AddMonoidAlgebra R E) ^ n * x = 0 → (p : AddMonoidAlgebra R E) ^ N * x = 0 := by
  let B := AddMonoidAlgebra R E
  refine ⟨1, fun n x hx => ?_⟩
  have h : ((p : R) ^ n) • x = 0 := by
    simpa only [Algebra.smul_def, map_pow, map_natCast] using hx
  have hz : (p : R) • x = 0 := by
    ext e
    have he := congrArg (fun y : B => y.coeff e) h
    have he' : (p : R) ^ n * x.coeff e = 0 := by
      simpa only [AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul, AddMonoidAlgebra.coeff_zero,
        Finsupp.zero_apply] using he
    simpa only [AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul, AddMonoidAlgebra.coeff_zero,
      Finsupp.zero_apply] using hR.p_mul_eq_zero_of_pow_mul_eq_zero R p n (x.coeff e) he'
  simpa only [Algebra.smul_def, map_natCast, pow_one] using hz

private theorem monomialAdicCompletionPerfectoid (hR : IsIntegralPerfectoid R p)
    (scale : E ≃+ E) (hs : ∀ e, scale e = p • e) :
    IsIntegralPerfectoid
      (AdicCompletion (Ideal.span {(p : AddMonoidAlgebra R E)}) (AddMonoidAlgebra R E)) p := by
  let T := AddMonoidAlgebra R E
  rcases hR with hR | ⟨hp, hc, ⟨π, u, hu⟩, hF, hker⟩
  · let : Subsingleton R := hR
    exact Or.inl (algebraMap T (AdicCompletion (Ideal.span {(p : T)}) T)).codomain_trivial
  · let : Fact (¬ IsUnit (p : R)) := ⟨hp⟩
    let := hc
    let k := PreTilt R p
    let W := WittVector p k
    let D := wittDeltaStructure p k
    have hD := wittDeltaStructure_isPerfect p k
    let θ := WittVector.fontaineTheta R p
    have hθ : Function.Surjective θ := surjective_fontaineTheta hF
    obtain ⟨d, hd, hker'⟩ := exists_distinguished_fontaine_kernel_generator R p hF hker π u hu
    obtain ⟨D', hD', hmap⟩ := exists_perfectMonomialDelta p D hD scale hs
    let f := AddMonoidAlgebra.mapRingHom E θ
    exact isIntegralPerfectoid_adicCompletion_of_distinguished_kernel D' hD'
      (algebraMap W (AddMonoidAlgebra W E) d) (hmap.map_isDistinguished hd)
      f (AddMonoidAlgebra.map_surjective θ.toAddMonoidHom hθ) (monomialMap_ker R θ d hker')

include hR in
/-- 有限変数に両立する p 冪根を添加した導来 p 完備環は、基底が整 perfectoid なら整 perfectoid。
方針：単項式表示で係数の Fontaine 商を延長し、指数の p 倍の同型で Frobenius を持ち上げる。
規約：係数の p 冪ねじれは有界性を使う。変数が空の場合も含む。
使われ方：BS 著者版 Proposition 8.5 の証明に現れる完備テンソル被覆。 -/
theorem polyRootAlgebra_isIntegralPerfectoid (r : ℕ) :
    IsIntegralPerfectoid (polyRootAlgebra p R r) p := by
  let E := Fin r → powerRootExponentMonoid p (Nat.Prime.pos (Fact.out : p.Prime))
  let M := AddMonoidAlgebra R E
  let scale : E ≃+ E := AddEquiv.piCongrRight (fun _ => powerRootExponentPrimeScaleEquiv p)
  have hs (e : E) : scale e = p • e := rfl
  have h := monomialAdicCompletionPerfectoid p R (E := E) hR scale hs
  let := principalCompletionCommRing M (p : M)
  let := principalCompletionAlgebra M (p : M)
  let j := boundedPrincipalCompletionAdicAlgEquiv M (p : M)
    (monomialBoundedTorsion p R (E := E) hR)
  let e := (ringCompletionFunctor p).mapIso (rawRootMonomialEquiv p R r).toCommRingCatIso
  exact isIntegralPerfectoid_of_ringEquiv p
    (j.toRingEquiv.symm.trans e.symm.commRingCatIsoToRingEquiv) h

end PolynomialPerfectoid

/-- 概要：S̃ = S ⊗̂_T T_∞（T → S、f で X_i ↦ f i）と S̃^n = (S̃^{⊗_S n+1})^∧。
方針：完備テンソル（A2 `BaseChangeAndTensor`、既存 `CompletedTensor` の芯）。
規約：S 代数。semiperfectoid 性（S/p の元は R/p 係数の x_i の多項式）は A5-4 `rootCover_isSemiperfectoid`。
使われ方：降下（A5-4）。 -/
def polyEvaluation (r : ℕ) (f : Fin r → S)
    (hS : SerrePositivity.DerivedCompletion.IsModuleComplete S (p : S) (ModuleCat.of S S)) :
    polyAlgebra p R r →+* S :=
  (completionLift p (CommRingCat.ofHom (MvPolynomial.eval₂Hom (algebraMap R S) f)) hS).hom

/-- T → S^∧ は S の選んだ変数を完備化へ送り評価する。S が完備なら completionUnitIso で T → S に戻る。 -/
def rootCoverAlgebra (r : ℕ) (f : Fin r → S) : Under (CommRingCat.of S) := by
  let T := CommRingCat.of (polyAlgebra p R r)
  let S' := completionRing p (CommRingCat.of S)
  let ev : T ⟶ S' := completionMap p (CommRingCat.ofHom (MvPolynomial.eval₂Hom (algebraMap R S) f))
  let j : T ⟶ CommRingCat.of (polyRootAlgebra p R r) := CommRingCat.ofHom (polyAlgebraToRoot p R r)
  exact Under.mk (completionUnit p _ ≫ Limits.pushout.inl ev j ≫ completionUnit p _)

/-- 多項式の根添加に沿って完備底変換した環。 -/
abbrev rootCover (r : ℕ) (f : Fin r → S) := ↥(rootCoverAlgebra p R S r f).right
instance (r : ℕ) (f : Fin r → S) : Algebra S (rootCover p R S r f) :=
  (rootCoverAlgebra p R S r f).hom.hom.toAlgebra

end SerrePositivity.BhattScholze.Perfectoidization.Derived
