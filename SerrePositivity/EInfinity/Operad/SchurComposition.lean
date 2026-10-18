module

public import SerrePositivity.EInfinity.Operad.Composition
public import SerrePositivity.EInfinity.Operad.TensorFamilyPowers

/-!
# Schur 対象の演算の生成射上の構成

概要：Berger–Moerdijk §1 の自由代数の演算を内側の arity を固定したテンソルから構成する。
方針：係数と入力を Koszul 対称性で集め、オペラッド合成と入力の連結を適用する。
規約：このファイルは生成射からの写像を構成する。coinvariant への降下は別の証明。
使われ方：Schur 対象上の自由代数の作用を余極限の普遍性で定義する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity

open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
open scoped BigOperators

variable {A : Type u} [CommRing A]

/-- 概要：各因子が二つのテンソルである有限族を、二つの有限テンソル族へ分ける同型（Berger–Moerdijk §1）。
方針：テンソル関手のモノイダル構造を、族の長さに関する再帰で適用する。
規約：並べ替えには既存の Koszul 符号が含まれる。
使われ方：自由代数の演算でオペラッドの係数と底の入力を集める。 -/
def tensorFamilyTensorIso : ∀ (n : ℕ) (V W : Fin n → Complex A),
    tensorFamily n (fun i => V i ⊗ W i) ≅ tensorFamily n V ⊗ tensorFamily n W
  | 0, _, _ => (λ_ (𝟙_ (Complex A))).symm
  | n + 1, V, W =>
    whiskerLeftIso (V 0 ⊗ W 0) (tensorFamilyTensorIso n (fun i => V i.succ) (fun i => W i.succ)) ≪≫
      { hom := tensorμ (V 0) (W 0) (tensorFamily n (fun i => V i.succ))
          (tensorFamily n (fun i => W i.succ))
        inv := tensorδ (V 0) (W 0) (tensorFamily n (fun i => V i.succ))
          (tensorFamily n (fun i => W i.succ))
        hom_inv_id := tensorμ_tensorδ _ _ _ _
        inv_hom_id := tensorδ_tensorμ _ _ _ _ }

namespace Operad

/-- 概要：Schur の各入力の生成射を有限テンソルして入力のテンソル冪へ送る（Berger–Moerdijk §1）。
方針：各 arity の構造射を先頭から順にテンソルし、空の族では恒等射を取る。
規約：内側 arity の有限族を固定する。
使われ方：自由代数の作用を生成射上で指定し、余極限へ降ろす。 -/
def schurInputGenerator (P : Operad A) (K : Complex A) (n : ℕ) (s : Fin n → ℕ) :
    tensorFamily n (fun i => P.arity (s i) ⊗ power K (s i)) ⟶
      power ((schurFunctor A P.sequence).obj K) n :=
  tensorFamilyGenerator ((schurFunctor A P.sequence).obj K)
    (fun i => P.arity i ⊗ power K i) (fun i => schurι A P.sequence K i) n s

/-- 概要：内側 arity を固定した Schur 演算の生成射（Berger–Moerdijk §1）。
方針：係数の有限族をオペラッドで合成し、入力のテンソル冪を連結して Schur 生成射へ送る。
規約：arity 0 と空の演算族を含む。余極限への降下や代数の公理をここでは主張しない。
使われ方：自由代数上の作用を生成射上で定義する。 -/
def schurOperationGenerator (P : Operad A) (K : Complex A) (n : ℕ) (s : Fin n → ℕ) :
    P.arity n ⊗ tensorFamily n (fun i => P.arity (s i) ⊗ power K (s i)) ⟶
      (schurFunctor A P.sequence).obj K :=
  (P.arity n ◁ (tensorFamilyTensorIso n (fun i => P.arity (s i)) (fun i => power K (s i))).hom) ≫
  (α_ (P.arity n) (tensorFamily n (fun i => P.arity (s i)))
    (tensorFamily n (fun i => power K (s i)))).inv ≫
  (P.composition n s ⊗ₘ (tensorPowerFamilyIso K n s).hom) ≫
  schurι A P.sequence K (∑ i, s i)

end Operad

end SerrePositivity.EInfinity
