module

public import SerrePositivity.EInfinity.Operad.SchurTensorGenerators
public import SerrePositivity.EInfinity.Operad.TensorColimitMorphisms

/-!
# Schur テンソル図式の射と入力ごとの置換

概要：Berger–Moerdijk §1 の自由代数の作用の降下で、図式の自己射を入力ごとの対称群作用で記述する。
方針：有限全単射の骨格の直積を arity 族で表示し、直積の射を各入力の置換へ分解する。
規約：空の入力族と arity 0 の入力を含む。
使われ方：Schur 演算の生成射の内側等変性から余錐の自然性を得る。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity

open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers

/-- 概要：Schur テンソル図式の対象と arity 族の間の同値（Berger–Moerdijk §1）。
方針：有限族と直積の同値に、標準有限集合とその濃度の対応を適用する。
規約：対象の型の同値であり、自己射の置換作用は保持する。
使われ方：図式の全対象の自然性を arity 族で調べる。 -/
def schurTensorArityEquiv (n : ℕ) : (Fin n → ℕ) ≃ tensorIndex FiniteBijection n where
  toFun s := tensorIndexOfFamily FiniteBijection n (fun i => FiniteBijection.of (s i))
  invFun j i := FiniteBijection.card (tensorIndexFamily FiniteBijection n j i)
  left_inv s := by
    funext i
    change FiniteBijection.card (tensorIndexFamily FiniteBijection n
      (tensorIndexOfFamily FiniteBijection n (fun i => FiniteBijection.of (s i))) i) = s i
    rw [tensorIndexFamily_ofFamily]
    rfl
  right_inv j := by
    apply (tensorIndexEquivFamily FiniteBijection n).injective
    change tensorIndexFamily FiniteBijection n
      (tensorIndexOfFamily FiniteBijection n (fun i =>
        FiniteBijection.of (FiniteBijection.card (tensorIndexFamily FiniteBijection n j i)))) = _
    rw [tensorIndexFamily_ofFamily]
    funext i
    exact FiniteBijection.of_card _

/-- 概要：arity 族で表した図式の自己射を入力ごとの置換へ送る（Berger–Moerdijk §1）。
方針：直積の先頭の射の全単射と、残りの入力の置換を再帰的に取り出す。
規約：各自己射は対応する標準有限集合の自己同型である。
使われ方：生成射の内側等変性に適用する置換族を得る。 -/
def schurTensorIndexPermutations : ∀ (n : ℕ) (s : Fin n → ℕ),
    (tensorIndexOfFamily FiniteBijection n (fun i => FiniteBijection.of (s i)) ⟶
      tensorIndexOfFamily FiniteBijection n (fun i => FiniteBijection.of (s i))) →
      ∀ i, Equiv.Perm (Fin (s i))
  | 0, _, _, i => Fin.elim0 i
  | n + 1, s, σ, i => Fin.cases (FiniteBijection.equivOfHom σ.1)
      (fun i => schurTensorIndexPermutations n (fun i => s i.succ) σ.2 i) i

variable {A : Type u} [CommRing A]

private lemma tensor_compare {X Y Z : Complex A} (f : X ⟶ X) (g : Y ⟶ Y)
    (h : Z ⟶ Z) (e : Y = Z) (hg : g ≫ eqToHom e = eqToHom e ≫ h) :
    (f ⊗ₘ g) ≫ (X ◁ eqToHom e) = (X ◁ eqToHom e) ≫ (f ⊗ₘ h) := by
  rw [tensorHom_comp_whiskerLeft, whiskerLeft_comp_tensorHom, hg]

/-- 概要：arity 族の自己射は各入力の diagonal action のテンソルである（Berger–Moerdijk §1）。
方針：外部テンソル図式の再帰で、先頭の全単射を標準置換として表示する。
規約：対象の比較に必要な等式の射を両辺に置く。
使われ方：Schur 図式上の余錐の自然性を内側の coinvariant 関係から証明する。 -/
lemma schurTensorDiagram_map_ofArity (P : SymmetricSequence (Complex A)) (K : Complex A)
    (n : ℕ) (s : Fin n → ℕ)
    (σ : tensorIndexOfFamily FiniteBijection n (fun i => FiniteBijection.of (s i)) ⟶
      tensorIndexOfFamily FiniteBijection n (fun i => FiniteBijection.of (s i))) :
    (schurTensorDiagram P K n).map σ ≫ eqToHom (schurTensorDiagram_obj_ofArity P K n s) =
      eqToHom (schurTensorDiagram_obj_ofArity P K n s) ≫
        tensorFamilyMap n (fun i =>
          P.map (FiniteBijection.permutation (s i) (schurTensorIndexPermutations n s σ i)) ⊗ₘ
            (permutationAction K (s i) (schurTensorIndexPermutations n s σ i)).asIso.hom) := by
  induction n with
  | zero =>
    change 𝟙 _ ≫ 𝟙 _ = 𝟙 _ ≫ 𝟙 _
    rfl
  | succ n ih =>
    rcases σ with ⟨σ₀, σtail⟩
    have he : eqToHom (schurTensorDiagram_obj_ofArity P K (n + 1) s) =
        (SymmetricSequence.level P (s 0) ⊗ power K (s 0)) ◁
          eqToHom (schurTensorDiagram_obj_ofArity P K n (fun i => s i.succ)) := by
      rw [whiskerLeft_eqToHom]
    have hs : σ₀ = FiniteBijection.permutation (s 0) (FiniteBijection.equivOfHom σ₀) :=
      (FiniteBijection.homOfEquiv_equivOfHom σ₀).symm
    have hh : (schurDiagram A P K).map σ₀ =
        P.map (FiniteBijection.permutation (s 0) (FiniteBijection.equivOfHom σ₀)) ⊗ₘ
          (permutationAction K (s 0) (FiniteBijection.equivOfHom σ₀)).asIso.hom := by
      rw [hs]
      exact congrArg (P.map (FiniteBijection.permutation (s 0) _) ⊗ₘ ·)
        (bijectionFunctor_map_permutation K (s 0) _)
    change (((schurDiagram A P K).map σ₀ ▷ (schurTensorDiagram P K n).obj _) ≫
      ((schurDiagram A P K).obj (FiniteBijection.of (s 0)) ◁
        (schurTensorDiagram P K n).map σtail)) ≫
          eqToHom (schurTensorDiagram_obj_ofArity P K (n + 1) s) =
      eqToHom (schurTensorDiagram_obj_ofArity P K (n + 1) s) ≫
        ((P.map (FiniteBijection.permutation (s 0) (FiniteBijection.equivOfHom σ₀)) ⊗ₘ
          (permutationAction K (s 0) (FiniteBijection.equivOfHom σ₀)).asIso.hom) ⊗ₘ
            tensorFamilyMap n (fun i =>
              P.map (FiniteBijection.permutation (s i.succ)
                (schurTensorIndexPermutations n (fun i => s i.succ) σtail i)) ⊗ₘ
              (permutationAction K (s i.succ)
                (schurTensorIndexPermutations n (fun i => s i.succ) σtail i)).asIso.hom))
    have hm : ((schurDiagram A P K).map σ₀ ▷ (schurTensorDiagram P K n).obj
        (tensorIndexOfFamily FiniteBijection n (fun i => FiniteBijection.of (s i.succ)))) ≫
        ((schurDiagram A P K).obj (FiniteBijection.of (s 0)) ◁
          (schurTensorDiagram P K n).map σtail) =
      (schurDiagram A P K).map σ₀ ⊗ₘ (schurTensorDiagram P K n).map σtail :=
        (tensorHom_def _ _).symm
    calc
      _ = ((schurDiagram A P K).map σ₀ ⊗ₘ (schurTensorDiagram P K n).map σtail) ≫
          ((SymmetricSequence.level P (s 0) ⊗ power K (s 0)) ◁
            eqToHom (schurTensorDiagram_obj_ofArity P K n (fun i => s i.succ))) :=
        congrArg₂ (· ≫ ·) hm he
      _ = _ := tensor_compare _ _ _ _ (ih (fun i => s i.succ) σtail)
      _ = _ := congrArg₂ (· ≫ ·) he.symm (congrArg (· ⊗ₘ _) hh)

end SerrePositivity.EInfinity
