module

public import SerrePositivity.Spectra.SymmetricSequence.TensorPowerSequence
public import SerrePositivity.DifferentialGraded.Complexes.MaurerCartanCurrying

/-!
# オペラッドの Schur 関手に必要なテンソル置換の自然性

概要：Berger–Moerdijk §1 の対称群による関係を複体射と両立させる。
方針：隣接交換の既存の自然性を、対称群の生成性で全置換へ延長する。
規約：既存の Koszul 対称性と反復テンソルを使う。
使われ方：対称列から構成する Schur 関手の射の自然性に用いる。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.EInfinity

open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers

variable (A : Type u) [CommRing A]

/-- 概要：反復テンソル上の全置換作用は複体射に関して自然（Berger–Moerdijk §1）。
方針：隣接交換に対する自然性と対称群のモノイドとしての生成性を使う。
規約：置換作用は既存の signed symmetry から構成したもの。
使われ方：Schur 関手の coinvariant 関係を射で保つ。 -/
lemma tensorPower_permutation_naturality {K L : Complex A} (f : K ⟶ L) (n : ℕ)
    (σ : Equiv.Perm (Fin n)) :
    TensorPowers.map f n ≫ (permutationAction L n σ).asIso.hom =
      (permutationAction K n σ).asIso.hom ≫ TensorPowers.map f n := by
  cases n with
  | zero => rfl
  | succ n =>
    have hs : σ ∈ Submonoid.closure
        (Set.range (fun i : Fin n => Equiv.swap i.castSucc i.succ)) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]
      exact Submonoid.mem_top _
    induction hs using Submonoid.closure_induction with
    | mem σ hs =>
      obtain ⟨i, rfl⟩ := hs
      change TensorPowers.map f (n + 1) ≫
        (permutationAction L (n + 1) (Coxeter.adjacentTransposition i)).asIso.hom =
          (permutationAction K (n + 1) (Coxeter.adjacentTransposition i)).asIso.hom ≫
            TensorPowers.map f (n + 1)
      rw [permutationAction_adjacent, permutationAction_adjacent]
      exact adjacentIso_naturality f n i
    | one => simp only [permutationAction_one, Category.comp_id, Category.id_comp]
    | mul σ τ _ _ hσ hτ =>
      rw [permutationAction_mul, permutationAction_mul, ← Category.assoc, hτ,
        Category.assoc, hσ, ← Category.assoc]

/-- 概要：有限全単射に沿うテンソル作用は複体射に関して自然（Berger–Moerdijk §1）。
方針：骨格の対象の等式を使い、全置換の自然性に帰着する。
規約：対称列の既存の共変関手の向きを保つ。
使われ方：反復テンソルを複体から対称列への関手にする。 -/
lemma tensorPower_bijection_naturality {K L : Complex A} (f : K ⟶ L)
    {S T : FiniteBijection} (σ : S ⟶ T) :
    TensorPowers.map f (FiniteBijection.card S) ≫ (bijectionFunctor L).map σ =
      (bijectionFunctor K).map σ ≫ TensorPowers.map f (FiniteBijection.card T) := by
  cases FiniteBijection.object_eq_of_hom σ
  simpa only [bijectionFunctor, FiniteBijection.familyFunctor, FiniteBijection.familyMap,
    finCongr_refl, Equiv.trans_refl, eqToHom_refl, Category.comp_id] using
      tensorPower_permutation_naturality A f (FiniteBijection.card S)
        (FiniteBijection.equivOfHom σ)

/-- 概要：複体射が誘導する反復テンソルの対称列の射（Berger–Moerdijk §1）。
方針：各 arity のテンソル冪の射を自然性で束ねる。
規約：Spectra の対称列とその置換作用を再利用する。
使われ方：Schur 関手の底の複体に関する関手性を与える。 -/
def tensorPowerSequenceMap {K L : Complex A} (f : K ⟶ L) :
    SymmetricSequence.tensorPowerSequence K ⟶ SymmetricSequence.tensorPowerSequence L where
  app S := TensorPowers.map f (FiniteBijection.card S)
  naturality {_S _T} σ := (tensorPower_bijection_naturality A f σ).symm

/-- 概要：反復テンソルの対称列は複体の圏から関手をなす（Berger–Moerdijk §1）。
方針：テンソル冪の恒等射・合成則を各 arity で用いる。
規約：値域は既存の `SymmetricSequence (Complex A)`。
使われ方：自由代数の底となる Schur 関手の構成に用いる。 -/
def tensorPowerSequenceFunctor : Complex A ⥤ SymmetricSequence (Complex A) where
  obj K := SymmetricSequence.tensorPowerSequence K
  map f := tensorPowerSequenceMap A f
  map_id K := by apply NatTrans.ext; funext S; exact TensorPowers.map_id K _
  map_comp f g := by apply NatTrans.ext; funext S; exact TensorPowers.map_comp f g _

end SerrePositivity.EInfinity
