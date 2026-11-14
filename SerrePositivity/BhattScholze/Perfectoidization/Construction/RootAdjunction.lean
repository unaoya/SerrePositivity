module

public import SerrePositivity.BhattScholze.Semiperfectoid.Quasiregular.RootFamilies.PowerRootPolynomial
public import SerrePositivity.BhattScholze.Andre.Transfinite.Colimit
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.RingInterface
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

open _root_.CategoryTheory

namespace SerrePositivity.BhattScholze.Perfectoidization.Derived

open _root_.SerrePositivity.BhattScholze.PerfectoidizationInterface

variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] (hR : IsIntegralPerfectoid R p)
variable (S : Type u) [CommRing S] [Algebra R S]

/-! ## (1) S̃（弱始対象の土台） -/

/-- 各 a に対する a − X_a^p − pY_a で生成される一段の関係イデアル。 -/
def _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStepIdeal (C : CommRingCat.{u}) : Ideal (MvPolynomial (C ⊕ C) C) :=
  Ideal.span (Set.range fun a : C => MvPolynomial.C a -
    MvPolynomial.X (Sum.inl a) ^ p - (p : MvPolynomial (C ⊕ C) C) * MvPolynomial.X (Sum.inr a))

/-- 概要：一段：S_1 = (S⟨X_s, Y_s : s ∈ S⟩/(s − X_s^p − pY_s))^∧（全元に p 乗根を mod p で添加）。
方針：`MvPolynomial (S ⊕ S) S` を関係 `s − X_s^p − p·Y_s` で割り、p 進完備化（`PrincipalCompletionH0 _ p` の H⁰、U4）。
規約：関手的（S の射で変数を送る）。
使われ方：`rootClosure`。 -/
abbrev _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rootAdjunctionStep (p : ℕ) (R S : Type u) [CommRing R] [CommRing S] :=
  ↥(completionRing p (CommRingCat.of
    (MvPolynomial (S ⊕ S) S ⧸ _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStepIdeal p (CommRingCat.of S))))

/-- 係数の包含を商と導来完備化へ送る。 -/
def _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rootAdjunctionStepUnit : S →+* _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rootAdjunctionStep p R S :=
  (completionUnit p _).hom.comp ((Ideal.Quotient.mk (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStepIdeal p _)).comp MvPolynomial.C)

instance : Algebra R (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rootAdjunctionStep p R S) :=
  ((_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rootAdjunctionStepUnit p R S).comp (algebraMap R S)).toAlgebra

/-- 概要：perfectoid 環 T への環射 S → T は、一段の根添加を通る。
方針：各元の像 t について t − y^p = pz を満たす y, z を選び、多項式環の普遍性と
導来完備化の普遍性を使う。
規約：延長は一意でない。
使われ方：`rootClosure_extends`。 -/
theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rootAdjunctionStep_extends (T : Type u) [CommRing T]
    (hT : _root_.SerrePositivity.IsIntegralPerfectoid T p) (g : S →+* T) :
    ∃ l : _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rootAdjunctionStep p R S →+* T, l.comp (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rootAdjunctionStepUnit p R S) = g := by
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
  have hker : _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStepIdeal p (CommRingCat.of S) ≤ RingHom.ker eval := by
    apply Ideal.span_le.mpr
    rintro _ ⟨a, rfl⟩
    change eval _ = 0
    simp only [eval, map_sub, map_pow, map_mul, map_natCast, MvPolynomial.eval₂Hom_C,
      MvPolynomial.eval₂Hom_X', Sum.elim_inl, Sum.elim_inr]
    rw [hz a, sub_self]
  let evalQuot := Ideal.Quotient.lift (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStepIdeal p (CommRingCat.of S)) eval hker
  let f := CommRingCat.ofHom evalQuot
  let l := completionLift p f (hT.isModuleComplete T p)
  refine ⟨l.hom, ?_⟩
  ext x
  change (completionUnit p _ ≫ l).hom (Ideal.Quotient.mk _ (MvPolynomial.C x)) = g x
  rw [completionLift_comp]
  exact MvPolynomial.eval₂Hom_C g (Sum.elim y z) x

/-- 概要：S̃ := (colim_k S_k)^∧（可算塔）。
方針：段の余極限（通常の環の sequential 余極限）の p 進完備化。
規約：R 代数、S → S̃。
使われ方：弱始対象（semiperfectoid 被覆による降下）、Lemma 8.8 の R₀ 上の根添加。 -/
def _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.completedStages : ℕ → CommRingCat.{u}
  | 0 => CommRingCat.of S
  | n + 1 => CommRingCat.of (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rootAdjunctionStep p R (completedStages n))

/-- 各完備な根添加の単位を後続射とする逐次図式。 -/
def _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.completedRootTower : ℕ ⥤ CommRingCat.{u} :=
  Functor.ofSequence (X := _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.completedStages p R S) fun n =>
    CommRingCat.ofHom (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rootAdjunctionStepUnit p R ((_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.completedStages p R S) n))

/-- 完備な根添加の逐次余極限の導来 p 完備化 H⁰。 -/
abbrev _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rootClosure := ↥(completionRing p (Limits.colimit (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.completedRootTower p R S)))

/-- 第零段を余極限に送り、導来完備化の単位と合成する。 -/
def _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rootClosureUnit : S →+* _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rootClosure p R S :=
  (completionUnit p _).hom.comp (Limits.colimit.ι (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.completedRootTower p R S) 0).hom

instance : Algebra R (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rootClosure p R S) :=
  ((_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rootClosureUnit p R S).comp (algebraMap R S)).toAlgebra

/-- 概要：S̃ は p 進完備（完備化なので）。
方針：`PrincipalCompletionH0` の完備性（既存 `principalCompletionH0_isCompleteModuleReflection`）。
規約：`IsModuleComplete`（HA/DerivedCompletion/Module）。
使われ方：κ 側の site の対象であること、Cor 8.12 の前提。 -/
theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rootClosure_isModuleComplete :
    SerrePositivity.DerivedCompletion.IsModuleComplete (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rootClosure p R S)
      (p : _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rootClosure p R S) (ModuleCat.of (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rootClosure p R S) (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rootClosure p R S)) := by
  exact completionRing_complete p _

/-- 概要：perfectoid 環 T への環射 S → T は、完備な根添加の余極限 S̃ を通る。
方針：各後続段に延長し、余極限と完備化の普遍性を使う。
規約：延長の存在を述べる。標的は perfectoid。
使われ方：弱始性、A6 の `exists_perfectoid_arcCover`。 -/
theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rootClosure_extends (T : Type u) [CommRing T]
    (hT : _root_.SerrePositivity.IsIntegralPerfectoid T p) (g : S →+* T) :
    ∃ l : _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rootClosure p R S →+* T, l.comp (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rootClosureUnit p R S) = g := by
  classical
  let F := _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.completedRootTower p R S
  let T' := CommRingCat.of T
  have step (n : ℕ) (f : F.obj n ⟶ T') :
      ∃ l : F.obj (n + 1) →+* T, l.comp (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rootAdjunctionStepUnit p R (F.obj n)) = f.hom := by
    letI : Algebra R (F.obj n) :=
      ((F.map (homOfLE (Nat.zero_le n))).hom.comp (algebraMap R S)).toAlgebra
    exact _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rootAdjunctionStep_extends p R (F.obj n) T hT f.hom
  let lift : ∀ n : ℕ, F.obj n ⟶ T' :=
    Nat.rec (CommRingCat.ofHom g) (fun n f => CommRingCat.ofHom (step n f).choose)
  let cocone : Limits.Cocone F :=
    { pt := T'
      ι := NatTrans.ofSequence lift (fun n => by
        change (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.completedRootTower p R S).map (homOfLE (Nat.le_add_right n 1)) ≫ lift (n + 1) =
          lift n ≫ 𝟙 T'
        have hmap : F.map (homOfLE (Nat.le_add_right n 1)) =
            CommRingCat.ofHom (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rootAdjunctionStepUnit p R (F.obj n)) :=
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
def _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStages (C : CommRingCat.{u}) : ℕ → CommRingCat.{u}
  | 0 => C
  | n + 1 =>
    let B := algebraicStages C n
    CommRingCat.of (MvPolynomial (B ⊕ B) B ⧸ _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStepIdeal p B)

/-- 根添加の係数包含を後続射とする、完備化前の逐次図式。 -/
def _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicTower (C : CommRingCat.{u}) : ℕ ⥤ CommRingCat.{u} :=
  Functor.ofSequence (X := _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStages p C) fun _n =>
    CommRingCat.ofHom ((Ideal.Quotient.mk (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStepIdeal p _)).comp MvPolynomial.C)

/-- 完備化前の代数的な根添加の逐次余極限。 -/
abbrev _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicRootClosure (C : Type u) [CommRing C] :=
  ↥(Limits.colimit (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicTower p (CommRingCat.of C)))

/-- 代数的な根添加の逐次余極限への第零段の射。 -/
def _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicRootClosureUnit (C : Type u) [CommRing C] : C →+* _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicRootClosure p C :=
  (Limits.colimit.ι (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicTower p (CommRingCat.of C)) 0).hom

/-- 完備化前の一段の根添加の環。 -/
abbrev _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.AlgebraicRootStep (p : ℕ) (C : CommRingCat.{u}) :=
  MvPolynomial (C ⊕ C) C ⧸ _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStepIdeal p C

/-- 係数と変数を同じ環射で送る、一段の根添加の写像。 -/
def _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStepMap {C C' : CommRingCat.{u}} (f : C ⟶ C') :
    _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.AlgebraicRootStep p C →+* _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.AlgebraicRootStep p C' := by
  let rename : MvPolynomial (C ⊕ C) C →+* MvPolynomial (C' ⊕ C') C' :=
    MvPolynomial.eval₂Hom (MvPolynomial.C.comp f.hom)
      (fun j => MvPolynomial.X (Sum.map f.hom f.hom j))
  refine Ideal.quotientMap (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStepIdeal p C') rename ?_
  apply Ideal.span_le.mpr
  rintro _ ⟨a, rfl⟩
  change rename (MvPolynomial.C a - MvPolynomial.X (Sum.inl a) ^ p -
      (p : MvPolynomial (C ⊕ C) C) * MvPolynomial.X (Sum.inr a)) ∈ _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStepIdeal p C'
  rw [map_sub, map_sub, map_pow, map_mul, map_natCast]
  dsimp only [rename]
  rw [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']
  exact Ideal.subset_span ⟨f.hom a, rfl⟩

@[simp] private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStepMap_coeff {C C' : CommRingCat.{u}} (f : C ⟶ C') (a : C) :
    _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStepMap p f (Ideal.Quotient.mk (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStepIdeal p C) (MvPolynomial.C a)) =
      Ideal.Quotient.mk (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStepIdeal p C') (MvPolynomial.C (f.hom a)) := by
  unfold _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStepMap
  erw [Ideal.quotientMap_mk]
  rw [MvPolynomial.eval₂Hom_C]
  rfl

@[simp] private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStepMap_var {C C' : CommRingCat.{u}} (f : C ⟶ C') (j : C ⊕ C) :
    _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStepMap p f (Ideal.Quotient.mk (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStepIdeal p C) (MvPolynomial.X j)) =
      Ideal.Quotient.mk (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStepIdeal p C')
        (MvPolynomial.X (Sum.map f.hom f.hom j)) := by
  unfold _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStepMap
  erw [Ideal.quotientMap_mk]
  rw [MvPolynomial.eval₂Hom_X']

@[simp] private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStepMap_id (C : CommRingCat.{u}) :
    _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStepMap p (𝟙 C) = RingHom.id (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.AlgebraicRootStep p C) := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro a
    simp
  · intro j
    cases j <;> simp

private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStepMap_comp {C C' C'' : CommRingCat.{u}} (f : C ⟶ C') (g : C' ⟶ C'') :
    _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStepMap p (f ≫ g) = (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStepMap p g).comp (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStepMap p f) := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro a
    simp
  · intro j
    cases j <;> simp

/-- 係数と変数の添字を同じ環射で送り、各段の関係を保つ。 -/
def _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStageMap {C C' : CommRingCat.{u}} (f : C ⟶ C') :
    ∀ n, _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStages p C n ⟶ _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStages p C' n
  | 0 => f
  | n + 1 => CommRingCat.ofHom (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStepMap p (algebraicStageMap f n))

private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStageMap_id (C : CommRingCat.{u}) (n : ℕ) :
    _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStageMap p (𝟙 C) n = 𝟙 _ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStageMap]
    apply CommRingCat.hom_ext
    change _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStepMap p (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStageMap p (𝟙 C) n) = RingHom.id _
    rw [ih, _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStepMap_id]

private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStageMap_comp {C C' C'' : CommRingCat.{u}}
    (f : C ⟶ C') (g : C' ⟶ C'') (n : ℕ) :
    _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStageMap p (f ≫ g) n = _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStageMap p f n ≫ _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStageMap p g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStageMap]
    apply CommRingCat.hom_ext
    change _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStepMap p (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStageMap p (f ≫ g) n) =
      (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStepMap p (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStageMap p g n)).comp
        (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStepMap p (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStageMap p f n))
    rw [ih, _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStepMap_comp]

private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicTower_succ (C : CommRingCat.{u}) (n : ℕ) :
    (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicTower p C).map (homOfLE (Nat.le_add_right n 1)) =
      CommRingCat.ofHom
        ((Ideal.Quotient.mk (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStepIdeal p (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStages p C n))).comp
          MvPolynomial.C) :=
  Functor.ofSequence_map_homOfLE_succ _ n

private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStageMap_succ {C C' : CommRingCat.{u}} (f : C ⟶ C') (n : ℕ) :
    _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStageMap p f (n + 1) =
      CommRingCat.ofHom (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStepMap p (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStageMap p f n)) := by
  rw [_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStageMap]

private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStageMap_naturality {C C' : CommRingCat.{u}} (f : C ⟶ C') (n : ℕ) :
    (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicTower p C).map (homOfLE (Nat.le_add_right n 1)) ≫
      _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStageMap p f (n + 1) =
    _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStageMap p f n ≫ (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicTower p C').map (homOfLE (Nat.le_add_right n 1)) := by
  rw [_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicTower_succ p C n, _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicTower_succ p C' n, _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStageMap_succ]
  apply CommRingCat.hom_ext
  exact RingHom.ext (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStepMap_coeff p (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStageMap p f n))

/-- 段ごとの再添字付けは、係数の包含に沿う後続射と可換。 -/
def _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicTowerMap {C C' : CommRingCat.{u}} (f : C ⟶ C') :
    _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicTower p C ⟶ _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicTower p C' :=
  NatTrans.ofSequence (F := _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicTower p C) (G := _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicTower p C')
    (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStageMap p f) (by exact _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStageMap_naturality p f)

/-- 代数的根添加の余極限へ段ごとの射を送る。 -/
def _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicRootClosureMap {C C' : Type u} [CommRing C] [CommRing C'] (f : C →+* C') :
    _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicRootClosure p C →+* _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicRootClosure p C' :=
  (Limits.colim.map (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicTowerMap p (CommRingCat.ofHom f))).hom

/-- 完備化前の代数的根添加は可換環の関手をなす。 -/
def _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicRootFunctor : CommRingCat.{u} ⥤ CommRingCat.{u} where
  obj C := Limits.colimit (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicTower p C)
  map f := Limits.colim.map (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicTowerMap p f)
  map_id C := by
    have h : _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicTowerMap p (𝟙 C) = 𝟙 _ := by
      apply NatTrans.ext
      funext n
      change _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStageMap p (𝟙 C) n = 𝟙 _
      exact _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStageMap_id p C n
    rw [h, CategoryTheory.Functor.map_id]
    rfl
  map_comp f g := by
    have h : _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicTowerMap p (f ≫ g) = _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicTowerMap p f ≫ _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicTowerMap p g := by
      apply NatTrans.ext
      funext n
      change _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStageMap p (f ≫ g) n = _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStageMap p f n ≫ _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStageMap p g n
      exact _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStageMap_comp p f g n
    rw [h, CategoryTheory.Functor.map_comp]

/-- 一段の代数的な根添加の写像を導来 p 完備化に送る。 -/
def _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.completedStepMap {C C' : CommRingCat.{u}} (f : C ⟶ C') :
    completionRing p (CommRingCat.of (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.AlgebraicRootStep p C)) ⟶
      completionRing p (CommRingCat.of (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.AlgebraicRootStep p C')) :=
  completionMap p (CommRingCat.ofHom (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStepMap p f))

private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.completedStepMap_id (C : CommRingCat.{u}) :
    _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.completedStepMap p (𝟙 C) = 𝟙 _ := by
  have h : CommRingCat.ofHom (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStepMap p (𝟙 C)) =
      𝟙 (CommRingCat.of (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.AlgebraicRootStep p C)) :=
    CommRingCat.hom_ext (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStepMap_id p C)
  rw [_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.completedStepMap, h, completionMap_id]

private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.completedStepMap_comp {C C' C'' : CommRingCat.{u}} (f : C ⟶ C') (g : C' ⟶ C'') :
    _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.completedStepMap p (f ≫ g) = _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.completedStepMap p f ≫ _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.completedStepMap p g := by
  have h : CommRingCat.ofHom (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStepMap p (f ≫ g)) =
      CommRingCat.ofHom (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStepMap p f) ≫ CommRingCat.ofHom (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStepMap p g) :=
    CommRingCat.hom_ext (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStepMap_comp p f g)
  simp only [_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.completedStepMap, h, completionMap_comp_map]

private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.completedStepMap_comp_unit {C C' : CommRingCat.{u}} (f : C ⟶ C') :
    CommRingCat.ofHom (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rootAdjunctionStepUnit p R C) ≫ _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.completedStepMap p f =
      f ≫ CommRingCat.ofHom (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rootAdjunctionStepUnit p R C') := by
  let j (A : CommRingCat.{u}) : A ⟶ CommRingCat.of (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.AlgebraicRootStep p A) :=
    CommRingCat.ofHom ((Ideal.Quotient.mk (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStepIdeal p A)).comp MvPolynomial.C)
  let k := CommRingCat.ofHom (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStepMap p f)
  have hj : j C ≫ k = f ≫ j C' :=
    CommRingCat.hom_ext (RingHom.ext (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStepMap_coeff p f))
  change (j C ≫ completionUnit p _) ≫ completionMap p k =
    f ≫ j C' ≫ completionUnit p _
  rw [Category.assoc, completionMap_comp, ← Category.assoc, hj, Category.assoc]

/-- 各完備段で変数を再添字付けし、導来完備化の写像を取る。 -/
def _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.completedStageMap {S' : Type u} [CommRing S'] (f : S →+* S') :
    ∀ n, _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.completedStages p R S n ⟶ _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.completedStages p R S' n
  | 0 => CommRingCat.ofHom f
  | n + 1 => _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.completedStepMap p (completedStageMap f n)

private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.completedStageMap_id (n : ℕ) :
    _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.completedStageMap p R S (RingHom.id S) n = 𝟙 _ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.completedStageMap, ih, _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.completedStepMap_id] <;> rfl

private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.completedStageMap_comp {S' S'' : Type u} [CommRing S'] [CommRing S'']
    (f : S →+* S') (g : S' →+* S'') (n : ℕ) :
    _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.completedStageMap p R S (g.comp f) n =
      _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.completedStageMap p R S f n ≫ _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.completedStageMap p R S' g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.completedStageMap, ih, _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.completedStepMap_comp] <;> rfl

omit [Fact p.Prime] [Algebra R S] in
private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.completedRootTower_succ (n : ℕ) :
    (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.completedRootTower p R S).map (homOfLE (Nat.le_add_right n 1)) =
      CommRingCat.ofHom (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rootAdjunctionStepUnit p R (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.completedStages p R S n)) :=
  Functor.ofSequence_map_homOfLE_succ _ n

/-- 完備な根添加の各段の写像は後続射と可換。 -/
def _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.completedRootTowerMap {S' : Type u} [CommRing S'] (f : S →+* S') :
    _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.completedRootTower p R S ⟶ _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.completedRootTower p R S' :=
  NatTrans.ofSequence (F := _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.completedRootTower p R S) (G := _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.completedRootTower p R S')
    (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.completedStageMap p R S f) (by
      intro n
      rw [_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.completedRootTower_succ p R S n, _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.completedRootTower_succ p R S' n, _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.completedStageMap]
      exact _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.completedStepMap_comp_unit p R (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.completedStageMap p R S f n))

/-- 完備根添加の余極限の写像を、さらに導来完備化へ送る。 -/
def _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rootClosureMap {S' : Type u} [CommRing S'] [Algebra R S'] (f : S →+* S') :
    _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rootClosure p R S →+* _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rootClosure p R S' :=
  (completionMap p (Limits.colim.map (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.completedRootTowerMap p R S f))).hom

/-- 完備根添加の写像は第零段の単位と可換。 -/
theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rootClosureMap_comp_unit {S' : Type u} [CommRing S'] [Algebra R S'] (f : S →+* S') :
    (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rootClosureMap p R S f).comp (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rootClosureUnit p R S) =
      (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rootClosureUnit p R S').comp f := by
  let k := _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.completedRootTowerMap p R S f
  have h : Limits.colimit.ι (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.completedRootTower p R S) 0 ≫ completionUnit p _ ≫
      completionMap p (Limits.colim.map k) =
      CommRingCat.ofHom f ≫ Limits.colimit.ι (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.completedRootTower p R S') 0 ≫
        completionUnit p _ := by
    have hι : Limits.colimit.ι (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.completedRootTower p R S) 0 ≫ Limits.colim.map k =
        CommRingCat.ofHom f ≫ Limits.colimit.ι (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.completedRootTower p R S') 0 :=
      Limits.ι_colimMap k 0
    rw [completionMap_comp, ← Category.assoc, hι]
    exact Category.assoc _ _ _
  exact congrArg (fun g : CommRingCat.of S ⟶ _ => g.hom) h

/-- 完備根添加の写像は恒等射を保つ。 -/
theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rootClosureMap_id : _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rootClosureMap p R S (RingHom.id S) = RingHom.id _ := by
  have h : _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.completedRootTowerMap p R S (RingHom.id S) = 𝟙 _ := by
    apply NatTrans.ext
    funext n
    exact _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.completedStageMap_id p R S n
  rw [_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rootClosureMap, h, CategoryTheory.Functor.map_id, completionMap_id]
  rfl

/-- 完備根添加の写像は環射の合成を保つ。 -/
theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rootClosureMap_comp {S' S'' : Type u} [CommRing S'] [Algebra R S']
    [CommRing S''] [Algebra R S''] (f : S →+* S') (g : S' →+* S'') :
    _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rootClosureMap p R S (g.comp f) = (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rootClosureMap p R S' g).comp (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rootClosureMap p R S f) := by
  have h : _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.completedRootTowerMap p R S (g.comp f) =
      _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.completedRootTowerMap p R S f ≫ _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.completedRootTowerMap p R S' g := by
    apply NatTrans.ext
    funext n
    exact _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.completedStageMap_comp p R S f g n
  simp only [_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rootClosureMap, h, CategoryTheory.Functor.map_comp, completionMap_comp_map]
  rfl

/-- 概要：代数的な根添加の余極限を mod p に移した環の Frobenius は全射。
方針：元を有限段から取り、次の段で添加した根を余極限と商へ送る。
使われ方：semiperfectoid 被覆による降下 の semiperfectoid 被覆への入力。 -/
theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicRootClosure_frobenius_surjective (C : Type u) [CommRing C] :
    Function.Surjective (fun x : ModP (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicRootClosure p C) p ↦ x ^ p) := by
  let F := _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicTower p (CommRingCat.of C)
  let q : _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicRootClosure p C →+* ModP (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicRootClosure p C) p := Ideal.Quotient.mk _
  intro x
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
  let : Limits.PreservesFilteredColimitsOfSize.{0, 0} (forget CommRingCat.{u}) :=
    Limits.preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  obtain ⟨n, a, ha⟩ := Limits.Concrete.colimit_exists_rep F c
  let qn := Ideal.Quotient.mk (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.algebraicStepIdeal p (F.obj n))
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
方針：`PrincipalCompletionH0 (MvPolynomial (Fin r) R) p` の H⁰（導来 perfectoid 化の界面の `completionRing` と同じ道具、U4）。
規約：R 代数。
使われ方：Lemma 8.6、semiperfectoid 被覆による降下 の降下、perfectoid 化の比較。 -/
abbrev _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.polyAlgebra (r : ℕ) := ↥(completionRing p (CommRingCat.of (MvPolynomial (Fin r) R)))
instance (r : ℕ) : Algebra R (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.polyAlgebra p R r) :=
  ((completionUnit p _).hom.comp MvPolynomial.C).toAlgebra
/-- p 完備化した多項式環における変数の像。 -/
def _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.polyAlgebraVar (r : ℕ) (i : Fin r) : _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.polyAlgebra p R r :=
  (completionUnit p _).hom (MvPolynomial.X i)

/-- 概要：T_∞ = R⟨X_1^{1/p^∞},…,X_r^{1/p^∞}⟩（p 完備化）と T → T_∞。
方針：`MvPolynomial (Fin r × ℕ) R` を `X_{i,n+1}^p − X_{i,n}` で割って p 進完備化する。
規約：変数 `polyRootAlgebraVar i n` は X_i^{1/p^n}。
使われ方：S̃ = S ⊗̂_T T_∞。 -/
def _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.polyRootIdeal (r : ℕ) : Ideal (MvPolynomial (Fin r × ℕ) R) :=
  Ideal.span (Set.range fun j : Fin r × ℕ =>
    MvPolynomial.X (j.1, j.2 + 1) ^ p - MvPolynomial.X j)

section PolynomialMonomials

open _root_.SerrePositivity.BhattScholze.Andre
open scoped _root_.BigOperators

variable (r : ℕ)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "G" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootExponentMonoid p hp
local notation "Q" => MvPolynomial (Fin r × ℕ) R ⧸ _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.polyRootIdeal p R r
local notation "M" => AddMonoidAlgebra R (Fin r → G)
local notation "q" => Ideal.Quotient.mk (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.polyRootIdeal p R r)

private abbrev _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rawRootVar (i : Fin r) (n : ℕ) : Q := q (MvPolynomial.X (i, n))

private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rawRootVar_pow (i : Fin r) (n : ℕ) :
    _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rawRootVar p R r i (n + 1) ^ p = _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rawRootVar p R r i n := by
  apply sub_eq_zero.mp
  change q (MvPolynomial.X (i, n + 1)) ^ p - q (MvPolynomial.X (i, n)) = 0
  rw [← map_pow, ← map_sub]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨(i, n), rfl⟩)

private def _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rawRootLift {B : Type u} [CommRing B] (f : R →+* B) (x : Fin r → ℕ → B)
    (hx : ∀ i n, x i (n + 1) ^ p = x i n) : Q →+* B := by
  let ev : MvPolynomial (Fin r × ℕ) R →+* B := MvPolynomial.eval₂Hom f (fun j => x j.1 j.2)
  refine Ideal.Quotient.lift (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.polyRootIdeal p R r) ev ?_
  change _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.polyRootIdeal p R r ≤ RingHom.ker ev
  apply Ideal.span_le.mpr
  rintro _ ⟨⟨i, n⟩, rfl⟩
  change ev _ = 0
  simp only [ev, map_sub, map_pow, MvPolynomial.eval₂Hom_X', hx, sub_self]

private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rawRootLift_coeff {B : Type u} [CommRing B] (f : R →+* B) (x : Fin r → ℕ → B)
    (hx : ∀ i n, x i (n + 1) ^ p = x i n) (a : R) :
    _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rawRootLift p R r f x hx (q (MvPolynomial.C a)) = f a := by
  unfold _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rawRootLift
  erw [Ideal.Quotient.lift_mk, MvPolynomial.eval₂Hom_C]

private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rawRootLift_var {B : Type u} [CommRing B] (f : R →+* B) (x : Fin r → ℕ → B)
    (hx : ∀ i n, x i (n + 1) ^ p = x i n) (i : Fin r) (n : ℕ) :
    _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rawRootLift p R r f x hx (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rawRootVar p R r i n) = x i n := by
  unfold _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rawRootLift
  erw [Ideal.Quotient.lift_mk, MvPolynomial.eval₂Hom_X']

private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rawRootHom_ext {B : Type u} [CommRing B] {f g : Q →+* B}
    (hC : ∀ a, f (q (MvPolynomial.C a)) = g (q (MvPolynomial.C a)))
    (hX : ∀ i n, f (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rawRootVar p R r i n) = g (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rawRootVar p R r i n)) : f = g := by
  apply Ideal.Quotient.ringHom_ext
  exact MvPolynomial.ringHom_ext hC (fun j => hX j.1 j.2)

private def _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rootMonomial (i : Fin r) (n : ℕ) : M :=
  AddMonoidAlgebra.single (Pi.single i (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootVariableExponent p hp n)) 1

private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rootMonomial_pow (i : Fin r) (n : ℕ) :
    _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rootMonomial p R r i (n + 1) ^ p = _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rootMonomial p R r i n := by
  rw [_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rootMonomial, _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rootMonomial, AddMonoidAlgebra.single_pow, one_pow]
  congr 1
  ext j
  by_cases h : j = i
  · subst j
    simp [_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootVariableExponent_nsmul]
  · simp [Pi.single_eq_of_ne h]

private def _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rawRootToMonomials : Q →+* M :=
  _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rawRootLift p R r (algebraMap R M) (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rootMonomial p R r) (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rootMonomial_pow p R r)

private def _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rootTupleEval : Multiplicative (Fin r → G) →* Q where
  toFun a := ∏ i, _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootExponentEvalHom p hp (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rawRootVar p R r i)
    (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rawRootVar_pow p R r i) (Multiplicative.ofAdd (a.toAdd i))
  map_one' := by
    change (∏ i, _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootExponentEvalHom p hp (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rawRootVar p R r i)
      (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rawRootVar_pow p R r i) (1 : Multiplicative G)) = 1
    simp
  map_mul' a b := by
    change (∏ i, _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootExponentEvalHom p hp (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rawRootVar p R r i)
      (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rawRootVar_pow p R r i)
      (Multiplicative.ofAdd (a.toAdd i) * Multiplicative.ofAdd (b.toAdd i))) = _
    simp only [map_mul, Finset.prod_mul_distrib]

private def _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rawRootFromMonomials : M →+* Q :=
  AddMonoidAlgebra.liftNCRingHom ((q).comp MvPolynomial.C) (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rootTupleEval p R r)
    (fun _ _ => Commute.all _ _)

private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rawRootFromMonomials_coeff (a : R) :
    _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rawRootFromMonomials p R r (algebraMap R M a) = q (MvPolynomial.C a) := by
  change AddMonoidAlgebra.liftNCRingHom ((q).comp MvPolynomial.C) (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rootTupleEval p R r) _
    (AddMonoidAlgebra.single 0 a) = _
  rw [AddMonoidAlgebra.liftNCRingHom_single]
  change q (MvPolynomial.C a) * _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rootTupleEval p R r 1 = q (MvPolynomial.C a)
  rw [map_one, mul_one]

private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rawRootFromMonomials_var (i : Fin r) (n : ℕ) :
    _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rawRootFromMonomials p R r (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rootMonomial p R r i n) = _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rawRootVar p R r i n := by
  rw [_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rawRootFromMonomials, _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rootMonomial, AddMonoidAlgebra.liftNCRingHom_single, map_one, one_mul]
  let v : Fin r → G := Pi.single i (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootVariableExponent p hp n)
  change _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rootTupleEval p R r (Multiplicative.ofAdd v) = _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rawRootVar p R r i n
  change (∏ j : Fin r, _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootExponentEvalHom p hp
    (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rawRootVar p R r j) (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rawRootVar_pow p R r j) (Multiplicative.ofAdd (v j))) = _
  dsimp only [v]
  rw [Finset.prod_eq_single i]
  · simp only [Pi.single_eq_same, _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootExponentEvalHom_variable]
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj]
    exact map_one _
  · simp

private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rawRootToMonomials_surjective : Function.Surjective (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rawRootToMonomials p R r) := by
  classical
  let f := _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rawRootToMonomials p R r
  let mono := AddMonoidAlgebra.of R (Fin r → G)
  have hcoeff (a : R) : f (q (MvPolynomial.C a)) = algebraMap R M a :=
    _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rawRootLift_coeff p R r _ _ _ _
  have hvar (i : Fin r) (n : ℕ) : f (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rawRootVar p R r i n) =
      mono (Multiplicative.ofAdd (Pi.single i (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootVariableExponent p hp n))) :=
    _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rawRootLift_var p R r _ _ _ _ _
  intro x
  induction x using AddMonoidAlgebra.induction_on with
  | of e =>
    have hcoord (i : Fin r) : ∃ x : Q, f x = mono (Multiplicative.ofAdd (Pi.single i (e i))) := by
      obtain ⟨n, k, hn⟩ := _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootExponent_exists_nsmul p hp (e i)
      refine ⟨_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rawRootVar p R r i n ^ k, ?_⟩
      rw [map_pow, hvar, ← map_pow]
      apply congrArg mono
      change Multiplicative.ofAdd (k • (Pi.single i (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootVariableExponent p hp n) :
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

private def _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rawRootMonomialEquiv : Q ≃+* M := by
  refine RingEquiv.ofBijective (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rawRootToMonomials p R r)
    ⟨?_, _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rawRootToMonomials_surjective p R r⟩
  have h : (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rawRootFromMonomials p R r).comp (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rawRootToMonomials p R r) = RingHom.id Q := by
    apply _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rawRootHom_ext p R r
    · intro a
      change _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rawRootFromMonomials p R r
        (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rawRootLift p R r _ _ _ (q (MvPolynomial.C a))) = q (MvPolynomial.C a)
      rw [_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rawRootLift_coeff, _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rawRootFromMonomials_coeff]
    · intro i n
      change _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rawRootFromMonomials p R r
        (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rawRootLift p R r _ _ _ (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rawRootVar p R r i n)) = _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rawRootVar p R r i n
      rw [_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rawRootLift_var, _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rawRootFromMonomials_var]
  have hleft : Function.LeftInverse (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rawRootFromMonomials p R r) (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rawRootToMonomials p R r) :=
    fun x => RingHom.congr_fun h x
  exact hleft.injective

end PolynomialMonomials

/-- 両立する根の関係で割った多項式環の導来 p 完備化 H⁰。 -/
abbrev _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.polyRootAlgebra (r : ℕ) :=
  ↥(completionRing p (CommRingCat.of (MvPolynomial (Fin r × ℕ) R ⧸ _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.polyRootIdeal p R r)))
instance (r : ℕ) : Algebra R (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.polyRootAlgebra p R r) :=
  ((completionUnit p _).hom.comp
    ((Ideal.Quotient.mk (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.polyRootIdeal p R r)).comp MvPolynomial.C)).toAlgebra

/-- i 番目の変数の n 段目の根を表す元。 -/
def _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.polyRootAlgebraVar (r : ℕ) (i : Fin r) (n : ℕ) : _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.polyRootAlgebra p R r :=
  (completionUnit p _).hom (Ideal.Quotient.mk (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.polyRootIdeal p R r) (MvPolynomial.X (i, n)))

/-- 多項式変数を根の第零段に送る完備環の射。 -/
def _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.polyAlgebraToRoot (r : ℕ) : _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.polyAlgebra p R r →+* _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.polyRootAlgebra p R r :=
  (completionMap p (CommRingCat.ofHom ((Ideal.Quotient.mk (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.polyRootIdeal p R r)).comp
    (MvPolynomial.rename (fun i : Fin r => (i, 0))).toRingHom))).hom

/-- 添加した各変数の根は p 乗で前の段の元に移る。 -/
theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.polyRootAlgebraVar_pow (r : ℕ) (i : Fin r) (n : ℕ) :
    _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.polyRootAlgebraVar p R r i (n + 1) ^ p = _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.polyRootAlgebraVar p R r i n := by
  let C := CommRingCat.of (MvPolynomial (Fin r × ℕ) R ⧸ _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.polyRootIdeal p R r)
  change (completionUnit p C).hom (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rawRootVar p R r i (n + 1)) ^ p =
    (completionUnit p C).hom (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rawRootVar p R r i n)
  rw [← map_pow, _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rawRootVar_pow]

/-- 通常の多項式変数は両立する根の第零段へ移る。 -/
theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.polyAlgebraToRoot_var (r : ℕ) (i : Fin r) :
    _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.polyAlgebraToRoot p R r (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.polyAlgebraVar p R r i) = _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.polyRootAlgebraVar p R r i 0 := by
  let f := CommRingCat.ofHom ((Ideal.Quotient.mk (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.polyRootIdeal p R r)).comp
    (MvPolynomial.rename (fun j : Fin r => (j, 0))).toRingHom)
  change (completionUnit p _ ≫ completionMap p f).hom (MvPolynomial.X i) = _
  rw [completionMap_comp]
  change (completionUnit p (CommRingCat.of (MvPolynomial (Fin r × ℕ) R ⧸ _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.polyRootIdeal p R r))).hom
    ((Ideal.Quotient.mk (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.polyRootIdeal p R r))
    (MvPolynomial.rename (fun j : Fin r => (j, 0)) (MvPolynomial.X i))) = _
  rw [MvPolynomial.rename_X]
  rfl

section PolynomialPerfectoid

open _root_.SerrePositivity.BhattScholze.Andre
open _root_.SerrePositivity.BhattScholze.Andre.Transfinite
open _root_.SerrePositivity.DerivedCompletion

universe v

variable {A : Type u} [CommRing A] {E : Type v} [AddCommMonoid E]

private def _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.monomialFrobenius (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A) (hD : D.IsPerfect) (scale : E ≃+ E) :
    AddMonoidAlgebra A E ≃+* AddMonoidAlgebra A E :=
  (AddMonoidAlgebra.mapRingEquiv E (D.frobeniusEquiv hD)).trans
    (AddMonoidAlgebra.mapDomainRingEquiv A scale)

private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.monomialFrobenius_single (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A) (hD : D.IsPerfect)
    (scale : E ≃+ E) (e : E) (a : A) :
    _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.monomialFrobenius p D hD scale (AddMonoidAlgebra.single e a) =
      AddMonoidAlgebra.single (scale e) (D.frobeniusLift a) := by
  change AddMonoidAlgebra.mapDomain scale
    (AddMonoidAlgebra.mapRingHom E D.frobeniusLift (AddMonoidAlgebra.single e a)) = _
  rw [AddMonoidAlgebra.mapRingHom_single, AddMonoidAlgebra.mapDomain_single]

private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.monomialFrobenius_mod_p (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A) (hD : D.IsPerfect)
    (scale : E ≃+ E) (hs : ∀ e, scale e = p • e) (x : AddMonoidAlgebra A E) :
    let q := Ideal.Quotient.mk (Ideal.span {(p : AddMonoidAlgebra A E)})
    q (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.monomialFrobenius p D hD scale x) = q x ^ p := by
  let B := AddMonoidAlgebra A E
  let q := Ideal.Quotient.mk (Ideal.span {(p : B)})
  have hpQ : (p : B ⧸ Ideal.span {(p : B)}) = 0 := by
    change q (p : B) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  have hc (a : A) :
      q (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.monomialFrobenius p D hD scale (algebraMap A (AddMonoidAlgebra A E) a)) =
        q (algebraMap A (AddMonoidAlgebra A E) a) ^ p := by
    have h : _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.monomialFrobenius p D hD scale (algebraMap A (AddMonoidAlgebra A E) a) =
        algebraMap A (AddMonoidAlgebra A E) (D.frobeniusLift a) := by
      change _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.monomialFrobenius p D hD scale (AddMonoidAlgebra.single 0 a) =
        AddMonoidAlgebra.single 0 (D.frobeniusLift a)
      rw [_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.monomialFrobenius_single, map_zero]
    rw [h, D.frobeniusLift_apply]
    simp only [map_add, map_mul, map_natCast, map_pow, hpQ, zero_mul, add_zero]
  change q (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.monomialFrobenius p D hD scale x) = q x ^ p
  induction x using AddMonoidAlgebra.induction_on with
  | of e =>
    change q (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.monomialFrobenius p D hD scale (AddMonoidAlgebra.single e 1)) =
      q (AddMonoidAlgebra.single e 1) ^ p
    rw [_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.monomialFrobenius_single, hs, map_one, ← map_pow, AddMonoidAlgebra.single_pow, one_pow]
  | add x y hx hy =>
    simp only [map_add, hx, hy]
    symm
    simpa only [hpQ, zero_mul, add_zero] using add_pow_prime_eq' (Fact.out : p.Prime) (q x) (q y)
  | smul a x hx =>
    rw [Algebra.smul_def]
    simp only [map_mul, hc, hx, mul_pow]

private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.exists_perfectMonomialDelta (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A) (hD : D.IsPerfect)
    (scale : E ≃+ E) (hs : ∀ e, scale e = p • e) :
    ∃ D' : _root_.SerrePositivity.BhattScholze.DeltaStructure p (AddMonoidAlgebra A E),
      D'.IsPerfect ∧ D.IsDeltaHom D' (algebraMap A (AddMonoidAlgebra A E)) := by
  let B := AddMonoidAlgebra A E
  let : Module.Free A B := Module.Free.of_basis (AddMonoidAlgebra.basis E A)
  have hpB : Function.Injective (fun a : B => (p : B) * a) := by
    simpa only [map_natCast, IsSMulRegular, smul_eq_mul] using
      (show IsSMulRegular A (p : A) from hD.p_mul_injective).of_flat (S := B)
  let φ := _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.monomialFrobenius p D hD scale
  obtain ⟨D', h, _⟩ := _root_.SerrePositivity.BhattScholze.DeltaStructure.existsUnique_of_mod_p hpB φ.toRingHom
    (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.monomialFrobenius_mod_p p D hD scale hs)
  refine ⟨D', ?_, _root_.SerrePositivity.BhattScholze.DeltaStructure.isDeltaHom_of_map_frobeniusLift (algebraMap A B) hpB ?_⟩
  · change Function.Bijective D'.frobeniusLift
    rw [h]
    exact φ.bijective
  · intro a
    rw [h]
    symm
    change _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.monomialFrobenius p D hD scale (AddMonoidAlgebra.single 0 a) =
      AddMonoidAlgebra.single 0 (D.frobeniusLift a)
    rw [_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.monomialFrobenius_single, map_zero]

private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.monomialMap_ker (f : A →+* R) (d : A) (hd : RingHom.ker f = Ideal.span {d}) :
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

private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.monomialBoundedTorsion (hR : _root_.SerrePositivity.IsIntegralPerfectoid R p) :
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

private theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.monomialAdicCompletionPerfectoid (hR : _root_.SerrePositivity.IsIntegralPerfectoid R p)
    (scale : E ≃+ E) (hs : ∀ e, scale e = p • e) :
    _root_.SerrePositivity.IsIntegralPerfectoid
      (AdicCompletion (Ideal.span {(p : AddMonoidAlgebra R E)}) (AddMonoidAlgebra R E)) p := by
  let T := AddMonoidAlgebra R E
  rcases hR with hR | ⟨hp, hc, ⟨π, u, hu⟩, hF, hker⟩
  · let : Subsingleton R := hR
    exact Or.inl (algebraMap T (AdicCompletion (Ideal.span {(p : T)}) T)).codomain_trivial
  · let : Fact (¬ IsUnit (p : R)) := ⟨hp⟩
    let := hc
    let k := PreTilt R p
    let W := WittVector p k
    let D := _root_.SerrePositivity.BhattScholze.wittDeltaStructure p k
    have hD := _root_.SerrePositivity.BhattScholze.wittDeltaStructure_isPerfect p k
    let θ := WittVector.fontaineTheta R p
    have hθ : Function.Surjective θ := surjective_fontaineTheta hF
    obtain ⟨d, hd, hker'⟩ := _root_.SerrePositivity.BhattScholze.exists_distinguished_fontaine_kernel_generator R p hF hker π u hu
    obtain ⟨D', hD', hmap⟩ := _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.exists_perfectMonomialDelta p D hD scale hs
    let f := AddMonoidAlgebra.mapRingHom E θ
    exact isIntegralPerfectoid_adicCompletion_of_distinguished_kernel D' hD'
      (algebraMap W (AddMonoidAlgebra W E) d) (hmap.map_isDistinguished hd)
      f (AddMonoidAlgebra.map_surjective θ.toAddMonoidHom hθ) (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.monomialMap_ker R θ d hker')

include hR in
/-- 有限変数に両立する p 冪根を添加した導来 p 完備環は、基底が整 perfectoid なら整 perfectoid。
方針：単項式表示で係数の Fontaine 商を延長し、指数の p 倍の同型で Frobenius を持ち上げる。
規約：係数の p 冪ねじれは有界性を使う。変数が空の場合も含む。
使われ方：BS 著者版 Proposition 8.5 の証明に現れる完備テンソル被覆。 -/
theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.polyRootAlgebra_isIntegralPerfectoid (r : ℕ) :
    _root_.SerrePositivity.IsIntegralPerfectoid (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.polyRootAlgebra p R r) p := by
  let E := Fin r → _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootExponentMonoid p (Nat.Prime.pos (Fact.out : p.Prime))
  let M := AddMonoidAlgebra R E
  let scale : E ≃+ E := AddEquiv.piCongrRight (fun _ => _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootExponentPrimeScaleEquiv p)
  have hs (e : E) : scale e = p • e := rfl
  have h := _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.monomialAdicCompletionPerfectoid p R (E := E) hR scale hs
  let := principalCompletionCommRing M (p : M)
  let := principalCompletionAlgebra M (p : M)
  let j := boundedPrincipalCompletionAdicAlgEquiv M (p : M)
    (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.monomialBoundedTorsion p R (E := E) hR)
  let e := (ringCompletionFunctor p).mapIso (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rawRootMonomialEquiv p R r).toCommRingCatIso
  exact _root_.SerrePositivity.BhattScholze.isIntegralPerfectoid_of_ringEquiv p
    (j.toRingEquiv.symm.trans e.symm.commRingCatIsoToRingEquiv) h

end PolynomialPerfectoid

/-- 概要：S̃ = S ⊗̂_T T_∞（T → S、f で X_i ↦ f i）と S̃^n = (S̃^{⊗_S n+1})^∧。
方針：完備テンソル（A2 `BaseChangeAndTensor`、既存 `CompletedTensor` の芯）。
規約：S 代数。semiperfectoid 性（S/p の元は R/p 係数の x_i の多項式）は semiperfectoid 被覆による降下 `rootCover_isSemiperfectoid`。
使われ方：降下（semiperfectoid 被覆による降下）。 -/
def _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.polyEvaluation (r : ℕ) (f : Fin r → S)
    (hS : SerrePositivity.DerivedCompletion.IsModuleComplete S (p : S) (ModuleCat.of S S)) :
    _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.polyAlgebra p R r →+* S :=
  (completionLift p (CommRingCat.ofHom (MvPolynomial.eval₂Hom (algebraMap R S) f)) hS).hom

/-- T → S^∧ は S の選んだ変数を完備化へ送り評価する。S が完備なら completionUnitIso で T → S に戻る。 -/
def _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rootCoverAlgebra (r : ℕ) (f : Fin r → S) : Under (CommRingCat.of S) := by
  let T := CommRingCat.of (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.polyAlgebra p R r)
  let S' := completionRing p (CommRingCat.of S)
  let ev : T ⟶ S' := completionMap p (CommRingCat.ofHom (MvPolynomial.eval₂Hom (algebraMap R S) f))
  let j : T ⟶ CommRingCat.of (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.polyRootAlgebra p R r) := CommRingCat.ofHom (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.polyAlgebraToRoot p R r)
  exact Under.mk (completionUnit p _ ≫ Limits.pushout.inl ev j ≫ completionUnit p _)

/-- 多項式の根添加に沿って完備底変換した環。 -/
abbrev _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rootCover (r : ℕ) (f : Fin r → S) := ↥(_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rootCoverAlgebra p R S r f).right
instance (r : ℕ) (f : Fin r → S) : Algebra S (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rootCover p R S r f) :=
  (_root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.rootCoverAlgebra p R S r f).hom.hom.toAlgebra

end SerrePositivity.BhattScholze.Perfectoidization.Derived
