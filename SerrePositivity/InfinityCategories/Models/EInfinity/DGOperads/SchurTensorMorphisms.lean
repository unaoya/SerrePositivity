module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.SchurTensorGenerators
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorColimitMorphisms

/-!
模型。文献の定義との比較は後で
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

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

/-- 概要：Schur テンソル図式の対象と arity 族の間の同値（Berger–Moerdijk §1）。
方針：有限族と直積の同値に、標準有限集合とその濃度の対応を適用する。
規約：対象の型の同値であり、自己射の置換作用は保持する。
使われ方：図式の全対象の自然性を arity 族で調べる。 -/
def schurTensorArityEquiv (n : ℕ) : (Fin n → ℕ) ≃ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndex _root_.SerrePositivity.FiniteBijection n where
  toFun s := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndexOfFamily _root_.SerrePositivity.FiniteBijection n (fun i => _root_.SerrePositivity.FiniteBijection.of (s i))
  invFun j i := _root_.SerrePositivity.FiniteBijection.card (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndexFamily _root_.SerrePositivity.FiniteBijection n j i)
  left_inv s := by
    funext i
    change _root_.SerrePositivity.FiniteBijection.card (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndexFamily _root_.SerrePositivity.FiniteBijection n
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndexOfFamily _root_.SerrePositivity.FiniteBijection n (fun i => _root_.SerrePositivity.FiniteBijection.of (s i))) i) = s i
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndexFamily_ofFamily]
    rfl
  right_inv j := by
    apply (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndexEquivFamily _root_.SerrePositivity.FiniteBijection n).injective
    change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndexFamily _root_.SerrePositivity.FiniteBijection n
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndexOfFamily _root_.SerrePositivity.FiniteBijection n (fun i =>
        _root_.SerrePositivity.FiniteBijection.of (_root_.SerrePositivity.FiniteBijection.card (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndexFamily _root_.SerrePositivity.FiniteBijection n j i)))) = _
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndexFamily_ofFamily]
    funext i
    exact _root_.SerrePositivity.FiniteBijection.of_card _

/-- 概要：arity 族で表した図式の自己射を入力ごとの置換へ送る（Berger–Moerdijk §1）。
方針：直積の先頭の射の全単射と、残りの入力の置換を再帰的に取り出す。
規約：各自己射は対応する標準有限集合の自己同型である。
使われ方：生成射の内側等変性に適用する置換族を得る。 -/
def schurTensorIndexPermutations : ∀ (n : ℕ) (s : Fin n → ℕ),
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndexOfFamily _root_.SerrePositivity.FiniteBijection n (fun i => _root_.SerrePositivity.FiniteBijection.of (s i)) ⟶
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndexOfFamily _root_.SerrePositivity.FiniteBijection n (fun i => _root_.SerrePositivity.FiniteBijection.of (s i))) →
      ∀ i, Equiv.Perm (Fin (s i))
  | 0, _, _, i => Fin.elim0 i
  | n + 1, s, σ, i => Fin.cases (_root_.SerrePositivity.FiniteBijection.equivOfHom σ.1)
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
lemma schurTensorDiagram_map_ofArity (P : _root_.SerrePositivity.SymmetricSequence (Complex A)) (K : Complex A)
    (n : ℕ) (s : Fin n → ℕ)
    (σ : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndexOfFamily _root_.SerrePositivity.FiniteBijection n (fun i => _root_.SerrePositivity.FiniteBijection.of (s i)) ⟶
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndexOfFamily _root_.SerrePositivity.FiniteBijection n (fun i => _root_.SerrePositivity.FiniteBijection.of (s i))) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurTensorDiagram P K n).map σ ≫ eqToHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurTensorDiagram_obj_ofArity P K n s) =
      eqToHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurTensorDiagram_obj_ofArity P K n s) ≫
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap n (fun i =>
          P.map (_root_.SerrePositivity.FiniteBijection.permutation (s i) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurTensorIndexPermutations n s σ i)) ⊗ₘ
            (permutationAction K (s i) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurTensorIndexPermutations n s σ i)).asIso.hom) := by
  induction n with
  | zero =>
    change 𝟙 _ ≫ 𝟙 _ = 𝟙 _ ≫ 𝟙 _
    rfl
  | succ n ih =>
    rcases σ with ⟨σ₀, σtail⟩
    have he : eqToHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurTensorDiagram_obj_ofArity P K (n + 1) s) =
        (_root_.SerrePositivity.SymmetricSequence.level P (s 0) ⊗ power K (s 0)) ◁
          eqToHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurTensorDiagram_obj_ofArity P K n (fun i => s i.succ)) := by
      rw [whiskerLeft_eqToHom]
    have hs : σ₀ = _root_.SerrePositivity.FiniteBijection.permutation (s 0) (_root_.SerrePositivity.FiniteBijection.equivOfHom σ₀) :=
      (_root_.SerrePositivity.FiniteBijection.homOfEquiv_equivOfHom σ₀).symm
    have hh : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurDiagram A P K).map σ₀ =
        P.map (_root_.SerrePositivity.FiniteBijection.permutation (s 0) (_root_.SerrePositivity.FiniteBijection.equivOfHom σ₀)) ⊗ₘ
          (permutationAction K (s 0) (_root_.SerrePositivity.FiniteBijection.equivOfHom σ₀)).asIso.hom := by
      rw [hs]
      exact congrArg (P.map (_root_.SerrePositivity.FiniteBijection.permutation (s 0) _) ⊗ₘ ·)
        (bijectionFunctor_map_permutation K (s 0) _)
    change (((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurDiagram A P K).map σ₀ ▷ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurTensorDiagram P K n).obj _) ≫
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurDiagram A P K).obj (_root_.SerrePositivity.FiniteBijection.of (s 0)) ◁
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurTensorDiagram P K n).map σtail)) ≫
          eqToHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurTensorDiagram_obj_ofArity P K (n + 1) s) =
      eqToHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurTensorDiagram_obj_ofArity P K (n + 1) s) ≫
        ((P.map (_root_.SerrePositivity.FiniteBijection.permutation (s 0) (_root_.SerrePositivity.FiniteBijection.equivOfHom σ₀)) ⊗ₘ
          (permutationAction K (s 0) (_root_.SerrePositivity.FiniteBijection.equivOfHom σ₀)).asIso.hom) ⊗ₘ
            _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap n (fun i =>
              P.map (_root_.SerrePositivity.FiniteBijection.permutation (s i.succ)
                (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurTensorIndexPermutations n (fun i => s i.succ) σtail i)) ⊗ₘ
              (permutationAction K (s i.succ)
                (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurTensorIndexPermutations n (fun i => s i.succ) σtail i)).asIso.hom))
    have hm : ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurDiagram A P K).map σ₀ ▷ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurTensorDiagram P K n).obj
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndexOfFamily _root_.SerrePositivity.FiniteBijection n (fun i => _root_.SerrePositivity.FiniteBijection.of (s i.succ)))) ≫
        ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurDiagram A P K).obj (_root_.SerrePositivity.FiniteBijection.of (s 0)) ◁
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurTensorDiagram P K n).map σtail) =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurDiagram A P K).map σ₀ ⊗ₘ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurTensorDiagram P K n).map σtail :=
        (tensorHom_def _ _).symm
    calc
      _ = ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurDiagram A P K).map σ₀ ⊗ₘ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurTensorDiagram P K n).map σtail) ≫
          ((_root_.SerrePositivity.SymmetricSequence.level P (s 0) ⊗ power K (s 0)) ◁
            eqToHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurTensorDiagram_obj_ofArity P K n (fun i => s i.succ))) :=
        congrArg₂ (· ≫ ·) hm he
      _ = _ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensor_compare _ _ _ _ (ih (fun i => s i.succ) σtail)
      _ = _ := congrArg₂ (· ≫ ·) he.symm (congrArg (· ⊗ₘ _) hh)

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
