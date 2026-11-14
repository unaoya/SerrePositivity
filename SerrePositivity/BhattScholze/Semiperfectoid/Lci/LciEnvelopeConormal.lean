module


public meta import SerrePositivity.Util.Citation
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import SerrePositivity.CommutativeAlgebra.Koszul.Generators
public import SerrePositivity.BhattScholze.Semiperfectoid.Lci.LciEnvelopeInvertP

/-!
# 関係の自由分解と余法類

## 概要
関係 f_i − d z_i の実際の Koszul 複体で微分を計算し、d 剰余の余法類を特定する。

## 方針
標準生成元の微分を零次同型で読み、生成元を殺す環射で移す。

## 規約
BS 著者版 Example 7.9、G-A3-7 の古典的な部分。実際のプリズムコホモロジーへの評価は別途行う。

## 使われ方
p 反転後の比較でフィルトレーションの一次が生成されることの計算。
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.BhattScholze

variable {R : Type u} {B : Type v} [CommRing R] [CommRing B]
variable {r : ℕ} (f z : Fin r → R) (d : R)
variable (ρ : R →+* B) (hd : ρ d = 0)

/-- 概要：自由分解の標準生成元 t̃_i の微分は f_i − d z_i。
方針：実際の Koszul 複体の生成元の微分公式を適用する。
規約：BS 著者版 Example 7.9 の関係列の写像錐模型。
使われ方：G-A3-7 の差商類を追跡する。 -/
theorem lciRelation_generator_d (i : Fin r) :
    (koszulZeroTermIso (fun j => f j - d * z j)).hom
      ((koszulComplex (fun j => f j - d * z j)).d (-1) 0
        (koszulGeneratorElement (fun j => f j - d * z j) i)) = f i - d * z i :=
  koszulGeneratorElement_d_coordinate _ i

local notation "J" => Ideal.span (Set.range (ρ ∘ f))
/-- 関係の自由分解の微分を指定した係数環で読む。 -/
@[expose] def lciRelationBoundaryCoordinate (i : Fin r) : B := ρ
  ((koszulZeroTermIso (fun j => f j - d * z j)).hom
    ((koszulComplex (fun j => f j - d * z j)).d (-1) 0
      (koszulGeneratorElement (fun j => f j - d * z j) i)))

include hd in
/-- 概要：微分の d 剰余は、指定した関係の剰余に一致する。
方針：微分公式に環射を適用し d を殺す。
規約：BS 著者版 Example 7.9 の一次の差商計算。
使われ方：余法加群への像を正規化する。 -/
theorem lciRelation_boundary_mod_generator (i : Fin r) :
    lciRelationBoundaryCoordinate f z d ρ i = ρ (f i) := by
  rw [lciRelationBoundaryCoordinate, lciRelation_generator_d, map_sub, map_mul, hd,
    zero_mul, sub_zero]

include hd in
/-- 微分の剰余が、関係の生成するイデアルに属すること。 -/
theorem lciRelation_boundary_mem (i : Fin r) : lciRelationBoundaryCoordinate f z d ρ i ∈ J := by
  rw [lciRelation_boundary_mod_generator f z d ρ hd]
  exact Ideal.subset_span ⟨i, rfl⟩

/-- 関係の自由分解の微分から得られる余法類。 -/
@[expose] def lciRelationConormalClass (i : Fin r) : (J).Cotangent :=
  (J).toCotangent ⟨lciRelationBoundaryCoordinate f z d ρ i, lciRelation_boundary_mem f z d ρ hd i⟩

/-- 概要：自由分解が与える余法類は f̄_i mod J²。
方針：微分の剰余公式を余法加群の商写像へ移す。
規約：BS 著者版 Example 7.9、G-A3-7 の一次の類の同定。
使われ方：分冪で生成される随伴次数環の一次生成元を指定する。 -/
theorem lciRelationConormalClass_eq (i : Fin r) :
    lciRelationConormalClass f z d ρ hd i =
      (J).toCotangent ⟨ρ (f i), Ideal.subset_span ⟨i, rfl⟩⟩ := by
  unfold lciRelationConormalClass
  congr 1
  exact Subtype.ext (lciRelation_boundary_mod_generator f z d ρ hd i)

/-- 概要：自由分解からの余法類は余法加群全体を生成する。
方針：関係の生成イデアルと一次の類の計算に既存の生成判定を適用する。
規約：BS 著者版 Example 7.9 の古典的な次数一の計算。
使われ方：G-A3-7 の分冪生成と稠密性への入力。 -/
theorem lciRelationConormalClass_span :
    Submodule.span B (Set.range (lciRelationConormalClass f z d ρ hd)) = ⊤ := by
  exact cotangent_span_eq_top_of_relation_classes (ρ ∘ f) rfl _
    (lciRelationConormalClass_eq f z d ρ hd)

/-- 概要：形式的な除算座標から余法加群への一次比較。
方針：関係の自由分解の微分が与える余法類を線形に延長する。
規約：BS 著者版 Example 7.9、G-A3-7 の古典的な座標比較。
使われ方：除算座標の一次の像をフィルトレーションの比較に渡す。 -/
@[expose] def lciRelationConormalLinearMap : (Fin r →₀ B) →ₗ[B] (J).Cotangent :=
  Finsupp.linearCombination B (lciRelationConormalClass f z d ρ hd)

/-- 概要：一次比較は各標準除算座標を f̄_i mod J² に送る。
方針：自由加群の標準単項式の公式と微分の余法類の計算を合成する。
規約：BS 著者版 Example 7.9 の [z_i] の座標の式。
使われ方：G-A3-7 の次数一の像を指定する。 -/
theorem lciRelationConormalLinearMap_single (i : Fin r) :
    lciRelationConormalLinearMap f z d ρ hd (Finsupp.single i 1) =
      (J).toCotangent ⟨ρ (f i), Ideal.subset_span ⟨i, rfl⟩⟩ := by
  rw [lciRelationConormalLinearMap, Finsupp.linearCombination_single, one_smul]
  exact lciRelationConormalClass_eq f z d ρ hd i

/-- 概要：除算座標の一次比較は余法加群に全射。
方針：線形結合の像は標準座標の張る部分加群であり、その部分加群は全体に一致する。
規約：BS 著者版 Example 7.9 の古典的な一次の生成。
使われ方：G-A3-7 の分冪による高い次数の持ち上げ。 -/
theorem lciRelationConormalLinearMap_surjective :
    Function.Surjective (lciRelationConormalLinearMap f z d ρ hd) := by
  rw [← LinearMap.range_eq_top, lciRelationConormalLinearMap,
    Finsupp.range_linearCombination]
  exact lciRelationConormalClass_span f z d ρ hd

end SerrePositivity.BhattScholze

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Ex 7.9" (partial := component) "BS-W15 K5（11-11）：envelope の側は本体（R の有界性を仮定する原典の形、D76。結論は有界な prism）。p 反転の議論 G-A3-7 の古典的な入力（余法加群、分冪の像の稠密性）も本体。Δ_R/A との同一視と HT 比較の適用は drafts の A3/LciAndQuasiregular"] _root_.SerrePositivity.BhattScholze.lciRelationConormalLinearMap_surjective
