module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineCechSource
public import SerrePositivity.BhattScholze.Delta.DividedPower.PDivision.PDivisionCompletion
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineCechSource
public import SerrePositivity.BhattScholze.Delta.Free.CrystallineTensorRegularity
public import SerrePositivity.HomologicalAlgebra.Cosimplicial.Algebra
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.AffineEnvelopeMaps

/-!
# 結晶側の多項式 Čech 模型

## 概要
自由 δ 座標の差の Frobenius 像を p で割って添加し、p 完備化する
（BS 著者版 Theorem 5.2 の結晶側の模型）。

## 方針
頂点を写すと、第 0 頂点との差は二つの差の差になる。完備 p 除算の普遍性を用いて
余単体構造を作る。

## 規約
基底は `(ℤ_p, (p))`。各項は古典的完備化した p 正則環。

## 使われ方
Frobenius に沿う結晶の橋と、余分な δ 座標の除去。
-/

public noncomputable section

open CategoryTheory SerrePositivity.DerivedCompletion

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable (p : ℕ) [Fact p.Prime] (r : ℕ)

local notation "Z" => (crystallineBasePrism p)
local notation "B" n => completedFreeDelta Z (AffineIndex r (SimplexCategory.len n))
local notation "D" n => completedFreeDeltaStructure Z (AffineIndex r (SimplexCategory.len n))
local notation "β" n => completedFreeDeltaBase Z (AffineIndex r (SimplexCategory.len n))

/-- 第 0 頂点との差の Frobenius 像。 -/
def crystallinePDDifference (n : SimplexCategory) (t : ULift.{u} (Fin r × Fin n.len)) :
    completedFreeDelta (crystallineBasePrism.{u} p) (AffineIndex.{u} r n.len) :=
  (D n).frobeniusLift
    (affineVariable Z r n.len t.down.1 t.down.2.succ - affineVariable Z r n.len t.down.1 0)

local notation "C" n =>
  ClassicalDeltaDivisionCompletion (D n) (p : B n) (crystallinePDDifference p r n)
local notation "E" n =>
  classicalDeltaDivisionStructure (D n) (p : B n) (crystallinePDDifference p r n)

/-- 自由 δ 環から結晶側の完備 p 除算模型への標準射。 -/
def pdDeltaUnit (n : SimplexCategory) :
    completedFreeDelta (crystallineBasePrism.{u} p) (AffineIndex.{u} r n.len) →+* C n :=
  classicalDeltaDivisionMap (D n) (p : B n) (crystallinePDDifference p r n)

theorem pdDeltaUnit_isDeltaHom (n : SimplexCategory) :
    (D n).IsDeltaHom (E n) (pdDeltaUnit.{u} p r n) :=
  classicalDeltaDivisionMap_isDeltaHom _ _ _

private theorem sourceMap_variable {m n : SimplexCategory} (θ : m ⟶ n)
    (j : Fin r) (i : Fin (m.len + 1)) :
    crystallineCechSourceMap.{u} p r θ (affineVariable Z r m.len j i) =
      affineVariable Z r n.len j (θ.toOrderHom i) :=
  (crystallineCechSourceMap_spec p r θ).2.2 ⟨(j, i)⟩

private def divideCopy (n : SimplexCategory) (j : Fin r) (i : Fin (n.len + 1)) : C n :=
  Fin.cases 0 (fun l => classicalPDivisionVariable (D n) (crystallinePDDifference p r n)
    ⟨(j, l)⟩) i

private theorem divideCopy_spec (n : SimplexCategory) (j : Fin r) (i : Fin (n.len + 1)) :
    (p : C n) * divideCopy p r n j i =
      pdDeltaUnit p r n ((D n).frobeniusLift
        (affineVariable Z r n.len j i - affineVariable Z r n.len j 0)) := by
  refine Fin.cases ?_ (fun l => ?_) i
  · simp [divideCopy, (Fact.out : Nat.Prime p).ne_zero]
  · exact classicalPDivisionVariable_relation (D n) (crystallinePDDifference p r n) ⟨(j, l)⟩

private theorem pdDeltaMap_divides {m n : SimplexCategory} (θ : m ⟶ n)
    (s : ULift.{u} (Fin r × Fin m.len)) :
    (p : C n) ∣ pdDeltaUnit p r n
      (crystallineCechSourceMap p r θ (crystallinePDDifference p r m s)) := by
  let j := s.down.1
  let i := θ.toOrderHom s.down.2.succ
  let i₀ := θ.toOrderHom 0
  refine ⟨divideCopy p r n j i - divideCopy p r n j i₀, ?_⟩
  rw [mul_sub, divideCopy_spec, divideCopy_spec]
  change pdDeltaUnit p r n
      (crystallineCechSourceMap p r θ ((D m).frobeniusLift
        (affineVariable Z r m.len j s.down.2.succ - affineVariable Z r m.len j 0))) = _
  rw [(crystallineCechSourceMap_spec p r θ).1.map_frobeniusLift,
    map_sub, sourceMap_variable, sourceMap_variable]
  rw [← map_sub, ← map_sub, sub_sub_sub_cancel_right]

private theorem pdDeltaMap_existsUnique {m n : SimplexCategory} (θ : m ⟶ n) :
    ∃! f : (C m) →+* (C n), (E m).IsDeltaHom (E n) f ∧
      f.comp (pdDeltaUnit.{u} p r m) =
        (pdDeltaUnit.{u} p r n).comp (crystallineCechSourceMap p r θ) := by
  let f := (pdDeltaUnit.{u} p r n).comp (crystallineCechSourceMap p r θ)
  have hf : (D m).IsDeltaHom (E n) f :=
    (pdDeltaUnit_isDeltaHom p r n).comp (crystallineCechSourceMap_spec p r θ).1
  let I : Ideal (C n) := Ideal.span {(p : C n)}
  let := classicalPDivision_isAdicComplete (D n) (crystallinePDDifference p r n)
  have hfP : f (p : B m) = (p : C n) := map_natCast f p
  have hreg : Function.Injective (fun x : C n => f (p : B m) * x) :=
    (congrArg (fun t : C n => Function.Injective (fun x : C n => t * x)) hfP).mpr
      (classicalPDivision_p_mul_injective (D n) (crystallinePDDifference p r n))
  have hdiv (s : ULift.{u} (Fin r × Fin m.len)) :
      f (p : B m) ∣ f (crystallinePDDifference p r m s) :=
    (congrArg (fun t : C n => t ∣ f (crystallinePDDifference p r m s)) hfP).mpr
      (pdDeltaMap_divides p r θ s)
  exact existsUnique_classicalDeltaDivisionHom (D m) (E n) (p : B m)
    (crystallinePDDifference p r m) f hf hreg hdiv I (Ideal.subset_span rfl)
    ((congrArg (fun t : C n => t ∈ I) hfP).mpr (Ideal.subset_span rfl))

private def pdDeltaMap {m n : SimplexCategory} (θ : m ⟶ n) : (C m) →+* (C n) :=
  (pdDeltaMap_existsUnique.{u} p r θ).choose

private theorem pdDeltaMap_spec {m n : SimplexCategory} (θ : m ⟶ n) :
    (E m).IsDeltaHom (E n) (pdDeltaMap.{u} p r θ) ∧
      (pdDeltaMap.{u} p r θ).comp (pdDeltaUnit p r m) =
        (pdDeltaUnit p r n).comp (crystallineCechSourceMap p r θ) :=
  (pdDeltaMap_existsUnique p r θ).choose_spec.1

/-- 結晶模型の各次数の完備環。 -/
def pdDeltaTerm (n : ℕ) : CommRingCat.{u} :=
  CommRingCat.of (C (SimplexCategory.mk n))

set_option maxHeartbeats 800000 in
-- 完備 p 除算環の型を Under の射の条件と照合する。
/-- Frobenius を施した差の p 除算により、結晶の余単体的代数を作る。 -/
def pdDeltaModel : SerrePositivity.Cosimplicial.CosimplicialAlgebra (crystallineBase.{u} p) where
  obj n := Under.mk (CommRingCat.ofHom ((pdDeltaUnit p r n).comp (β n)))
  map {m n} θ := Under.homMk (CommRingCat.ofHom (pdDeltaMap p r θ)) (by
    apply CommRingCat.hom_ext
    change (pdDeltaMap p r θ).comp ((pdDeltaUnit p r m).comp (β m)) =
      (pdDeltaUnit p r n).comp (β n)
    rw [← RingHom.comp_assoc, (pdDeltaMap_spec p r θ).2, RingHom.comp_assoc,
      (crystallineCechSourceMap_spec p r θ).2.1])
  map_id n := by
    apply Under.UnderMorphism.ext
    apply CommRingCat.hom_ext
    obtain ⟨f, hf, hu⟩ := pdDeltaMap_existsUnique.{u} p r (𝟙 n)
    have hB : crystallineCechSourceMap.{u} p r (𝟙 n) = RingHom.id (B n) :=
      congrArg CommRingCat.Hom.hom ((crystallineCechSource.{u} p r).map_id n)
    change pdDeltaMap p r (𝟙 n) = RingHom.id (C n)
    refine (hu _ (pdDeltaMap_spec p r _)).trans (hu _ ⟨(E n).isDeltaHom_id, ?_⟩).symm
    rw [hB, RingHom.id_comp, RingHom.comp_id]
  map_comp {l m n} f g := by
    apply Under.UnderMorphism.ext
    apply CommRingCat.hom_ext
    obtain ⟨h, _, hu⟩ := pdDeltaMap_existsUnique.{u} p r (f ≫ g)
    have hB : crystallineCechSourceMap.{u} p r (f ≫ g) =
        (crystallineCechSourceMap p r g).comp (crystallineCechSourceMap p r f) :=
      congrArg CommRingCat.Hom.hom ((crystallineCechSource.{u} p r).map_comp f g)
    change pdDeltaMap p r (f ≫ g) = (pdDeltaMap p r g).comp (pdDeltaMap p r f)
    refine (hu _ (pdDeltaMap_spec p r _)).trans (hu _
      ⟨(pdDeltaMap_spec p r g).1.comp (pdDeltaMap_spec p r f).1, ?_⟩).symm
    rw [RingHom.comp_assoc, (pdDeltaMap_spec p r f).2, ← RingHom.comp_assoc,
      (pdDeltaMap_spec p r g).2, RingHom.comp_assoc, hB]

/-- 結晶側模型の台の余単体的可換環。 -/
abbrev pdDeltaRings :=
  pdDeltaModel.{u} p r ⋙ Under.forget (CommRingCat.of (crystallineBase.{u} p))

end SerrePositivity.BhattScholze.Prismatic

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Thm 5.2" (partial := component) "結晶の橋の mod p のコホモロジー同型（有限変数・I＝(p)）。比較同型そのものは D68 の段 3 と結晶サイト（a1-design §11） ／ 11-10 更新。整係数の版と W(C)・J の多項式の版（Thm 6.4 で使う形）も本体 ／ 11-12 夜更新（§5・§6 の見直し）"] _root_.SerrePositivity.BhattScholze.Prismatic.pdDeltaModel
