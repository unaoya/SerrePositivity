module

public import SerrePositivity.BhattScholze.Perfectoidization.Derived.Interface
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# 完備な可換環への根添加

## 概要
全元に mod p で p 乗根を添加する完備な一段と可算塔、完備化前の代数的な根添加、
有限変数の両立する根の環と完備な底変換を構成する。

## 方針
多項式環の商の普遍性、逐次余極限、既存の導来完備化 H⁰ の普遍性を用いる。

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

variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R]
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
  let q := Ideal.Quotient.mk (polyRootIdeal p R r)
  have h : q (MvPolynomial.X (i, n + 1)) ^ p = q (MvPolynomial.X (i, n)) := by
    apply sub_eq_zero.mp
    rw [← map_pow, ← map_sub]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.subset_span ⟨(i, n), rfl⟩
  let C := CommRingCat.of (MvPolynomial (Fin r × ℕ) R ⧸ polyRootIdeal p R r)
  change (completionUnit p C).hom (q (MvPolynomial.X (i, n + 1))) ^ p =
    (completionUnit p C).hom (q (MvPolynomial.X (i, n)))
  rw [← map_pow, h]
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
