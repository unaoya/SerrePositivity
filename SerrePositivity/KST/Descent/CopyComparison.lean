module

public import SerrePositivity.KST.Descent.PresheafAction
public import SerrePositivity.KST.Descent.PermutationRepresentation

/-!
# コピーへの指定制限と (3.8) の置換比較

## 概要
各コピーの包含による引き戻しを積への比較とし、コピーの置換作用と両立させる。
この比較が全単射なら、推移的なコピーの fold の降下は指定対角写像の計算から従う。

## 方針
前層の反変合成で作用と比較の可換性を証明する。
不変部分での比較を、定数族への対角写像と一致させる。

## 規約
コピーへの比較の全単射性は、非交和に対する前層の降下から供給する責務。
このファイルでは任意の前層が非交和を積へ送ると仮定しない。
hG の構成やその有理化との比較は別に必要。

## 使われ方
論文 (3.8) の π_* 側の比較を、実際の非交和の指定射に接続する。
-/

@[expose] public section

universe u v w t

open CategoryTheory Opposite Representation

namespace SerrePositivity.KST.Descent.GradedPresheaf

variable {C : Type u} [Category.{v} C] {Coefficient : Type w}
variable (L : GradedPresheaf.{u, v, w, t} C Coefficient)
variable {B W : C} {I : Type*}

/-- 概要：コピーの包含による前層の積への指定比較（論文 (3.8)）。
方針：各包含による引き戻しを並べる。
規約：比較の全単射性は定義に含めない。
使われ方：非交和の前層比較と置換表現の接続。 -/
def copyEvaluation (H : Coefficient) (n : ℤ) (inclusions : I → (B ⟶ W)) :
    (L H n).obj (op W) →ₗ[ℚ] (I → (L H n).obj (op B)) :=
  LinearMap.pi fun i ↦ L.pullback H n (inclusions i)

/-- 概要：コピーへの指定比較は置換表現への同変写像（論文 (3.8)）。
方針：包含と置換自己同型の合成へ反変前層を適用する。
規約：左作用は逆元の引き戻しと、逆元の添字置換。
使われ方：前層の非交和比較を不変部分へ制限する。 -/
def copyEvaluationIntertwining (H : Coefficient) (n : ℤ) (inclusions : I → (B ⟶ W))
    {G : Type*} [Group G] [MulAction G I] (action : G →* Aut W)
    (permutation : ∀ g i, inclusions i ≫ (action g).asIso.hom = inclusions (g • i)) :
    IntertwiningMap (L.pullbackRepresentation H n action)
      (permutationRepresentation G I ((L H n).obj (op B))) where
  toLinearMap := L.copyEvaluation H n inclusions
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    funext i
    change L.pullback H n (inclusions i) (L.pullback H n (action g⁻¹).asIso.hom x) =
      L.pullback H n (inclusions (g⁻¹ • i)) x
    have h := congrArg (fun k ↦ L.pullback H n k x) (permutation g⁻¹ i)
    simpa only [pullback_comp, LinearMap.comp_apply] using h

/-- 概要：fold の引き戻しを各コピーへ制限すると定数族（論文 (3.8)）。
方針：各包含と fold の合成が恒等射であることに反変前層を適用する。
規約：指定されたコピーへの制限を用いる。
使われ方：前層の比較と対角写像の一致。 -/
theorem copyEvaluation_fold (H : Coefficient) (n : ℤ) (inclusions : I → (B ⟶ W))
    (fold : W ⟶ B) (components : ∀ i, inclusions i ≫ fold = 𝟙 B)
    (x : (L H n).obj (op B)) :
    L.copyEvaluation H n inclusions (L.pullback H n fold x) = fun _ ↦ x := by
  funext i
  change L.pullback H n (inclusions i) (L.pullback H n fold x) = x
  calc
    _ = L.pullback H n (inclusions i ≫ fold) x :=
      (LinearMap.congr_fun (L.pullback_comp H n (inclusions i) fold) x).symm
    _ = L.pullback H n (𝟙 B) x := congrArg (fun k ↦ L.pullback H n k x) (components i)
    _ = x := by rw [L.pullback_id]; rfl

/-- 概要：fold の固定部分への比較は指定対角写像と可換（論文 (3.8)）。
方針：不変部分の値を忘れると前補題の定数族になる。
規約：不変部分への比較も幾何学的な fold の引き戻しそのもの。
使われ方：推移的なコピーの固定部分への同型。 -/
theorem copyEvaluation_fixed_fold (H : Coefficient) (n : ℤ) (inclusions : I → (B ⟶ W))
    (fold : W ⟶ B) (components : ∀ i, inclusions i ≫ fold = 𝟙 B)
    {G : Type*} [Group G] [MulAction G I] (action : G →* Aut W)
    (permutation : ∀ g i, inclusions i ≫ (action g).asIso.hom = inclusions (g • i))
    (over_base : ∀ g, (action g).asIso.hom ≫ fold = fold) (x : (L H n).obj (op B)) :
    invariantMap (L.copyEvaluationIntertwining H n inclusions action permutation)
      (L.invariantSubmoduleEquiv H n action (L.invariantComparison H n fold action over_base x)) =
        permutationDiagonal G I ((L H n).obj (op B)) x := by
  apply Subtype.ext
  exact L.copyEvaluation_fold H n inclusions fold components x

/-- 概要：非交和比較の全単射性から推移的なコピーの fold の全次数降下（論文 (3.8)）。
方針：不変部分の比較の全単射性と、指定対角写像の全単射性から元の比較を消去する。
規約：コピー比較の全単射性を明示し、任意の前層には主張しない。
使われ方：軌道正方形の中項のコピー側の比較。 -/
theorem copyFold_piDescent_of_evaluation (inclusions : I → (B ⟶ W))
    (fold : W ⟶ B) (components : ∀ i, inclusions i ≫ fold = 𝟙 B)
    {G : Type*} [Group G] [Finite G] [MulAction G I]
    [MulAction.IsPretransitive G I] [Nonempty I] (action : G →* Aut W)
    (permutation : ∀ g i, inclusions i ≫ (action g).asIso.hom = inclusions (g • i))
    (over_base : ∀ g, (action g).asIso.hom ≫ fold = fold)
    (evaluation_bijective : ∀ H n, Function.Bijective (L.copyEvaluation H n inclusions)) :
    L.PiDescent fold action over_base := by
  intro H n
  let evaluation := L.copyEvaluationIntertwining H n inclusions action permutation
  have evaluation_fixed_bijective : Function.Bijective (invariantMap evaluation) :=
    ⟨invariantMap_injective evaluation (evaluation_bijective H n).1,
      invariantMap_surjective evaluation (evaluation_bijective H n).2⟩
  let fixed := L.invariantSubmoduleEquiv H n action
  have comm :
      (invariantMap evaluation ∘ fixed) ∘ L.invariantComparison H n fold action over_base =
        permutationDiagonal G I ((L H n).obj (op B)) := by
    funext x
    exact L.copyEvaluation_fixed_fold H n inclusions fold components action permutation over_base x
  have composite_bijective : Function.Bijective
      ((invariantMap evaluation ∘ fixed) ∘ L.invariantComparison H n fold action over_base) := by
    rw [comm]
    exact permutationDiagonal_bijective G I ((L H n).obj (op B))
  exact (Function.Bijective.of_comp_iff'
    (evaluation_fixed_bijective.comp fixed.bijective) _).mp composite_bijective

end SerrePositivity.KST.Descent.GradedPresheaf
