module

public import SerrePositivity.KST.DerivedBlowup.FreeKoszulBaseChange

/-!
概要：KST §3.1 の自由 Koszul 生成加群の係数変更を総外積代数の実際の射として固定する。
方針：既存の外積底変更射と自由生成加群の標準比較を合成し、生成元の像を計算する。
規約：微分とは独立の総外積代数の射。
使われ方：dg 底変更の Hom 写像の比較と連続した係数変更の合成則。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open scoped TensorProduct

variable {R S : Type u} [CommRing R] [CommRing S] {I : Type} [DecidableEq I]

/-- 概要：自由生成加群の各係数を環射で送る写像。
方針：有限台関数の値域写像を使う。
規約：KST §3.1。使われ方：総外積の係数変更の生成元公式。 -/
def freeGeneratorScalarMap (φ : R →+* S) (m : I →₀ R) : I →₀ S :=
  Finsupp.mapRange φ (map_zero φ) m

/-- 概要：自由生成加群の底変更同型は 1⊗m を係数写像へ送る。
方針：finsuppScalarRight の純粋 tensor 公式を各座標で評価する。
規約：KST §3.1。使われ方：外積係数変更の生成元の像。 -/
theorem freeKoszulBaseChangeGeneratorEquiv_one_tmul (φ : R →+* S) (m : I →₀ R) :
    letI := φ.toAlgebra
    freeKoszulBaseChangeGeneratorEquiv φ I ((1 : S) ⊗ₜ[R] m) = freeGeneratorScalarMap φ m := by
  let := φ.toAlgebra
  ext j
  simp [freeKoszulBaseChangeGeneratorEquiv,
    freeGeneratorScalarMap, Algebra.smul_def]
  rfl

/-- 概要：自由生成加群の総外積代数の係数変更射。
方針：1⊗生成元への外積射と自由生成加群の標準底変更同型を合成する。
規約：KST §3.1、元の係数環上の代数射として構成する。
使われ方：Koszul dg 底変更の総外積上の計算先。 -/
def freeExteriorScalarMap (φ : R →+* S) :
    letI := φ.toAlgebra
    ExteriorAlgebra R (I →₀ R) →ₐ[R] ExteriorAlgebra S (I →₀ S) := by
  letI := φ.toAlgebra
  exact ((ExteriorAlgebra.map
    (freeKoszulBaseChangeGeneratorEquiv φ I).toLinearMap).restrictScalars R).comp
    (exteriorOfBaseChangeAux (R := R) (S := S) (M := I →₀ R))

/-- 概要：総外積の係数変更は生成加群上で各係数を環射に送る。
方針：二つの外積射の生成元公式と自由生成加群比較の 1⊗m 公式を使う。
規約：KST §3.1。使われ方：連続した係数変更の合成比較。 -/
theorem freeExteriorScalarMap_ι (φ : R →+* S) (m : I →₀ R) :
    letI := φ.toAlgebra
    freeExteriorScalarMap φ (ExteriorAlgebra.ι R m) =
      ExteriorAlgebra.ι S (freeGeneratorScalarMap φ m) := by
  let := φ.toAlgebra
  change ExteriorAlgebra.map (freeKoszulBaseChangeGeneratorEquiv φ I).toLinearMap
    (exteriorOfBaseChangeAux (ExteriorAlgebra.ι R m)) = _
  rw [exteriorOfBaseChangeAux_ι, ExteriorAlgebra.map_apply_ι]
  exact congrArg (ExteriorAlgebra.ι S) (freeKoszulBaseChangeGeneratorEquiv_one_tmul φ m)

/-- 概要：総外積の係数変更は基底係数を指定環射で送る。
方針：代数準同型の係数保存とスカラー塔の構造射の式を使う。
規約：KST §3.1。使われ方：外積射の合成を係数上で確認する。 -/
theorem freeExteriorScalarMap_algebraMap (φ : R →+* S) (r : R) :
    letI := φ.toAlgebra
    freeExteriorScalarMap (I := I) φ (algebraMap R (ExteriorAlgebra R (I →₀ R)) r) =
      algebraMap S (ExteriorAlgebra S (I →₀ S)) (φ r) := by
  let := φ.toAlgebra
  rw [(freeExteriorScalarMap (I := I) φ).commutes]
  exact IsScalarTower.algebraMap_apply R S (ExteriorAlgebra S (I →₀ S)) r

variable {T : Type u} [CommRing T]

/-- 概要：恒等環射による総外積の係数変更は恒等。
方針：係数と生成元の像を外積代数の帰納法で比較する。
規約：KST §3.1。使われ方：自由 Koszul の恒等 dg 係数変更。 -/
theorem freeExteriorScalarMap_id (z : ExteriorAlgebra R (I →₀ R)) :
    freeExteriorScalarMap (RingHom.id R) z = z := by
  induction z using ExteriorAlgebra.induction with
  | algebraMap r => exact freeExteriorScalarMap_algebraMap (RingHom.id R) r
  | ι m =>
    rw [freeExteriorScalarMap_ι]
    congr 1
    ext j
    rfl
  | mul x y hx hy => simp only [map_mul, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

omit [DecidableEq I] in
/-- 概要：自由生成加群の係数写像は環射の合成を保つ。
方針：有限台関数を各座標で比較する。
規約：KST §3.1。使われ方：二段階の外積係数変更の比較。 -/
theorem freeGeneratorScalarMap_comp (φ : R →+* S) (ψ : S →+* T) (m : I →₀ R) :
    freeGeneratorScalarMap ψ (freeGeneratorScalarMap φ m) =
      freeGeneratorScalarMap (ψ.comp φ) m := by
  ext j
  rfl

/-- 概要：総外積の係数変更は連続した環射の合成を保つ。
方針：係数・生成元・積・和による外積代数の帰納法を使う。
規約：KST §3.1、係数環の違う代数射を元の像として比較する。
使われ方：自由 Koszul dg 模型の係数変更の合成則。 -/
theorem freeExteriorScalarMap_comp (φ : R →+* S) (ψ : S →+* T)
    (z : ExteriorAlgebra R (I →₀ R)) :
    freeExteriorScalarMap ψ (freeExteriorScalarMap φ z) =
      freeExteriorScalarMap (ψ.comp φ) z := by
  induction z using ExteriorAlgebra.induction with
  | algebraMap r =>
    rw [freeExteriorScalarMap_algebraMap, freeExteriorScalarMap_algebraMap,
      freeExteriorScalarMap_algebraMap]
    rfl
  | ι m =>
    rw [freeExteriorScalarMap_ι, freeExteriorScalarMap_ι, freeExteriorScalarMap_ι,
      freeGeneratorScalarMap_comp]
  | mul x y hx hy => simp only [map_mul, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

end SerrePositivity.KST.DerivedBlowup
