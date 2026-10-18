module

public import SerrePositivity.EInfinity.Operad.SchurTensorColimit

/-!
# Schur テンソル余極限の arity 族による生成射

概要：Berger–Moerdijk §1 の自由代数の作用の生成射を、余極限の構造射と比較する。
方針：各 arity の標準有限集合を独立な入力の添字に送り、有限テンソルの構造射を同定する。
規約：対象の等式による移送を明示する。
使われ方：生成射上の演算の式を Schur テンソル余極限の降下に接続する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity

open CategoryTheory Limits MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers

variable {A : Type u} [CommRing A]

/-- 概要：arity 族で添字付けた Schur テンソル図式の対象（Berger–Moerdijk §1）。
方針：添字の直積と有限族の同値を用い、各標準有限集合で Schur 図式を評価する。
規約：arity 0 も許す。
使われ方：自由代数の作用の生成射の始域を余極限の図式の対象として読む。 -/
lemma schurTensorDiagram_obj_ofArity (P : SymmetricSequence (Complex A)) (K : Complex A)
    (n : ℕ) (s : Fin n → ℕ) :
    (schurTensorDiagram P K n).obj
      (tensorIndexOfFamily FiniteBijection n (fun i => FiniteBijection.of (s i))) =
        tensorFamily n (fun i => SymmetricSequence.level P (s i) ⊗ power K (s i)) := by
  change (tensorIndexDiagram (schurDiagram A P K) n).obj _ = _
  rw [tensorIndexDiagram_obj, tensorIndexFamily_ofFamily]
  rfl

namespace Operad

/-- 概要：arity 族の Schur 生成射は余極限の構造射に一致する（Berger–Moerdijk §1）。
方針：一般のテンソル余錐の構造射の式を標準有限集合の族に適用する。
規約：始域の対象の比較に必要な等式による移送を明示する。
使われ方：自由代数の作用の生成射上の計算を余極限の降下の式から得る。 -/
lemma schurTensorLeg_ofArity (P : Operad A) (K : Complex A) (n : ℕ) (s : Fin n → ℕ) :
    eqToHom (schurTensorDiagram_obj_ofArity P.sequence K n s) ≫ P.schurInputGenerator K n s =
      schurTensorLeg P.sequence K n
        (tensorIndexOfFamily FiniteBijection n (fun i => FiniteBijection.of (s i))) := by
  induction n with
  | zero => exact Category.id_comp _
  | succ n ih =>
    have he : eqToHom (schurTensorDiagram_obj_ofArity P.sequence K (n + 1) s) =
        (P.arity (s 0) ⊗ power K (s 0)) ◁
          eqToHom (schurTensorDiagram_obj_ofArity P.sequence K n (fun i => s i.succ)) := by
      rw [whiskerLeft_eqToHom]
    change eqToHom (schurTensorDiagram_obj_ofArity P.sequence K (n + 1) s) ≫
      (schurι A P.sequence K (s 0) ⊗ₘ P.schurInputGenerator K n (fun i => s i.succ)) =
        schurι A P.sequence K (s 0) ⊗ₘ
          schurTensorLeg P.sequence K n
            (tensorIndexOfFamily FiniteBijection n (fun i => FiniteBijection.of (s i.succ)))
    rw [he, whiskerLeft_comp_tensorHom, ih]

/-- 概要：降下射は arity 族で指定した生成射上の値を取る（Berger–Moerdijk §1）。
方針：標準生成射と余極限の構造射の同定に、降下射の計算則を適用する。
規約：係数は左に固定し、対象の等式による移送を前置する。
使われ方：自由代数の作用の明示式を、余極限による構成から検証する。 -/
@[reassoc]
lemma schurInputGenerator_desc (P : Operad A) (K C Y : Complex A) (n : ℕ)
    (f : ∀ j, C ⊗ (schurTensorDiagram P.sequence K n).obj j ⟶ Y)
    (hf : ∀ {j k} (σ : j ⟶ k),
      (C ◁ (schurTensorDiagram P.sequence K n).map σ) ≫ f k = f j)
    (s : Fin n → ℕ) :
    (C ◁ eqToHom (schurTensorDiagram_obj_ofArity P.sequence K n s)) ≫
      (C ◁ P.schurInputGenerator K n s) ≫
        schurTensorDesc P.sequence K C Y n f hf =
          f (tensorIndexOfFamily FiniteBijection n (fun i => FiniteBijection.of (s i))) := by
  rw [← MonoidalCategory.whiskerLeft_comp_assoc, P.schurTensorLeg_ofArity]
  exact schurTensorLeg_desc P.sequence K C Y n f hf _

end Operad

end SerrePositivity.EInfinity
