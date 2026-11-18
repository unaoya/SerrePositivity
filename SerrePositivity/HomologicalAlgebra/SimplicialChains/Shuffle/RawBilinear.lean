module

public import SerrePositivity.HomologicalAlgebra.SimplicialChains.Shuffle.Values
public import SerrePositivity.HomologicalAlgebra.SimplicialChains.AlexanderWhitney.Unnormalized

/-!
# 自由単体加群上の shuffle 双線形写像

概要：Berger–Fresse §1.1.3 の一般の shuffle 和を自由加群上で双線形に延長する。
方針：二つの自由加群の標準生成元に順に線形延長する。
規約：出力だけは正規化鎖とし、入力の正規化は後で行う。
使われ方：一般の shuffle の正規化鎖上の成分を構成する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.SimplicialChains.Shuffle

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open scoped _root_.Simplicial

variable (A : Type u) [CommRing A]

/-- 概要：自由単体加群上の shuffle の双線形延長（Berger–Fresse §1.1.3）。
方針：二つの自由加群の普遍性を内部の線形写像加群に適用する。
規約：両入力は非正規化、出力は積の正規化鎖。
使われ方：Moore 正規化へ降ろす前の成分。 -/
def rawBilinear (X Y : SSet.{0}) (p q : ℕ) :
    _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.simplexModule A X p →ₗ[A]
      _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.simplexModule A Y q →ₗ[A]
        (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A (X ⊗ Y)).X (p + q) :=
  (ModuleCat.freeDesc
    (M := ModuleCat.of A (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.simplexModule A Y q →ₗ[A]
      (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A (X ⊗ Y)).X (p + q)))
    (↾fun x : ULift.{u} (X _⦋p⦌) =>
      (ModuleCat.freeDesc
        (M := (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A (X ⊗ Y)).X (p + q))
        (↾fun y : ULift.{u} (Y _⦋q⦌) => _root_.SerrePositivity.SimplicialChains.Shuffle.value A X Y p q x.down y.down)).hom)).hom

/-- 概要：自由生成元上の双線形延長は shuffle 和（Berger–Fresse §1.1.3）。
方針：二回の自由加群の線形延長を標準生成元で評価する。
規約：入力の退化性を仮定しない。
使われ方：退化消滅と正規化への降下。 -/
@[simp] lemma rawBilinear_freeMk (X Y : SSet.{0}) (p q : ℕ)
    (x : X _⦋p⦌) (y : Y _⦋q⦌) :
    _root_.SerrePositivity.SimplicialChains.Shuffle.rawBilinear A X Y p q (ModuleCat.freeMk (ULift.up x)) (ModuleCat.freeMk (ULift.up y)) =
      _root_.SerrePositivity.SimplicialChains.Shuffle.value A X Y p q x y := by
  change (ModuleCat.freeDesc
    (M := ModuleCat.of A (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.simplexModule A Y q →ₗ[A]
      (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A (X ⊗ Y)).X (p + q))) _ (ModuleCat.freeMk (ULift.up x)))
    (ModuleCat.freeMk (ULift.up y)) = _
  rw [ModuleCat.freeDesc_apply]
  exact ModuleCat.freeDesc_apply _ _

/-- 概要：第一の退化写像は自由 shuffle の双線形写像で零（Berger–Fresse §1.1.3）。
方針：両自由生成元で検査し、退化入力の shuffle 和の消滅を使う。
規約：第二の入力は任意の自由鎖である。
使われ方：第一の正規化射影への不変性。 -/
lemma σ_rawBilinear_left (X Y : SSet.{0}) (p q : ℕ) (i : Fin (p + 1)) :
    ((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).obj X).σ i ≫
      ModuleCat.ofHom (_root_.SerrePositivity.SimplicialChains.Shuffle.rawBilinear A X Y (p + 1) q) = 0 := by
  apply ModuleCat.free_hom_ext
  intro ⟨x⟩
  change _root_.SerrePositivity.SimplicialChains.Shuffle.rawBilinear A X Y (p + 1) q
    (((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).obj X).σ i (ModuleCat.freeMk (ULift.up x))) = 0
  erw [ModuleCat.free_map_apply]
  apply LinearMap.ext
  intro y
  have he : ModuleCat.ofHom (_root_.SerrePositivity.SimplicialChains.Shuffle.rawBilinear A X Y (p + 1) q
      (ModuleCat.freeMk (ULift.up (X.σ i x)))) =
      (0 : _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.simplexModule A Y q ⟶
        (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A (X ⊗ Y)).X (p + 1 + q)) := by
    apply ModuleCat.free_hom_ext
    intro ⟨z⟩
    change _root_.SerrePositivity.SimplicialChains.Shuffle.rawBilinear A X Y (p + 1) q (ModuleCat.freeMk (ULift.up (X.σ i x)))
      (ModuleCat.freeMk (ULift.up z)) = 0
    rw [_root_.SerrePositivity.SimplicialChains.Shuffle.rawBilinear_freeMk, _root_.SerrePositivity.SimplicialChains.Shuffle.value_σ_left]
  exact congrArg (fun φ => φ y) he

/-- 概要：第二の退化写像は自由 shuffle の双線形写像で零（Berger–Fresse §1.1.3）。
方針：両自由生成元で検査し、第二の退化入力の消滅を使う。
規約：内部の線形写像加群へは変数を反転して入れる。
使われ方：第二の正規化射影への不変性。 -/
lemma σ_rawBilinear_right (X Y : SSet.{0}) (p q : ℕ) (i : Fin (q + 1)) :
    ((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).obj Y).σ i ≫
      ModuleCat.ofHom (_root_.SerrePositivity.SimplicialChains.Shuffle.rawBilinear A X Y p (q + 1)).flip = 0 := by
  apply ModuleCat.free_hom_ext
  intro ⟨y⟩
  change (_root_.SerrePositivity.SimplicialChains.Shuffle.rawBilinear A X Y p (q + 1)).flip
    (((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).obj Y).σ i (ModuleCat.freeMk (ULift.up y))) = 0
  erw [ModuleCat.free_map_apply]
  apply LinearMap.ext
  intro x
  have he : ModuleCat.ofHom ((_root_.SerrePositivity.SimplicialChains.Shuffle.rawBilinear A X Y p (q + 1)).flip
      (ModuleCat.freeMk (ULift.up (Y.σ i y)))) =
      (0 : _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.simplexModule A X p ⟶
        (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A (X ⊗ Y)).X (p + (q + 1))) := by
    apply ModuleCat.free_hom_ext
    intro ⟨z⟩
    change _root_.SerrePositivity.SimplicialChains.Shuffle.rawBilinear A X Y p (q + 1) (ModuleCat.freeMk (ULift.up z))
      (ModuleCat.freeMk (ULift.up (Y.σ i y))) = 0
    rw [_root_.SerrePositivity.SimplicialChains.Shuffle.rawBilinear_freeMk, _root_.SerrePositivity.SimplicialChains.Shuffle.value_σ_right]
  exact congrArg (fun φ => φ x) he

end SerrePositivity.SimplicialChains.Shuffle
