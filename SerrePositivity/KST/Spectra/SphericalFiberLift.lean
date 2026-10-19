module

public import SerrePositivity.KST.Spectra.SphericalBoundaryReduction
public import SerrePositivity.KST.Spectra.SphericalBoundaryAlternating

/-!
概要：fiber に球面的な面を持つ単体を、射影先を固定して簡約する。
方針：既存の球面的境界の簡約ホーンを底の退化単体に沿って相対充填する。
規約：底の単体を変更しない。fiber 内の面の積と向きは既存のものを使う。
使われ方：Goerss–Jardine I §8、VIII §1。連結射と交代和の相対境界関係。
-/

@[expose] public section
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial

namespace SerrePositivity.KST.Spectra

/-- 概要：底の境界定数単体の、全ての面が fiber に入る球面的な持ち上げ。
方針：射影の等式と fiber の各代表の全空間への包含を記録する。
規約：面の実際の次数は n+1。
使われ方：Goerss–Jardine I §8。相対的な交代境界関係の入力。 -/
structure SphericalFiberLift {E B : SSet.{u}} (p : E ⟶ B) (e : E _⦋0⦌) {n : ℕ}
    (s : B.PtSimplex (n + 2) (p.app _ e))
    (a : Fin (n + 3) → (KanFiber p (p.app _ e)).PtSimplex (n + 1) (fiberPoint p e)) where
  map : (Δ[n + 2] : SSet.{u}) ⟶ E
  map_comp : map ≫ p = s.map
  face_eq (j : Fin (n + 3)) : stdSimplex.δ j ≫ map = (a j).map ≫ fiberι p (p.app _ e)

namespace SphericalFiberLift

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {E B : SSet.{u}} {p : E ⟶ B} {e : E _⦋0⦌} {n : ℕ}
  {s : B.PtSimplex (n + 3) (p.app _ e)}
  {a : Fin (n + 4) → (KanFiber p (p.app _ e)).PtSimplex (n + 2) (fiberPoint p e)}

/-- fiber の境界定数単体を全空間へ含める。 -/
def totalSimplex (t : (KanFiber p (p.app _ e)).PtSimplex (n + 2) (fiberPoint p e)) :
    E.PtSimplex (n + 2) e := mapSimplex (fiberι p (p.app _ e)) (fiberι_point p e) t

@[simp]
lemma totalSimplex_const : totalSimplex (p := p) (e := e)
    (RelativeMorphism.const : (KanFiber p (p.app _ e)).PtSimplex (n + 2) (fiberPoint p e)) =
      .const := mapSimplex_const _ _

/-- fiber 内の積の充填を全空間へ含める。 -/
def totalMulStruct {f g h : (KanFiber p (p.app _ e)).PtSimplex (n + 2) (fiberPoint p e)}
    {i : Fin (n + 2)} (r : PtSimplex.MulStruct f g h i) :
    PtSimplex.MulStruct (totalSimplex f) (totalSimplex g) (totalSimplex h) i :=
  mapMulStruct (fiberι p (p.app _ e)) (fiberι_point p e) r

/-- 相対的な境界を全空間での球面的境界として読む。 -/
def totalBoundary (T : SphericalFiberLift p e s a) : SphericalBoundary (fun j ↦ totalSimplex (a j))
    where
  map := T.map
  face_eq := T.face_eq

variable {i : Fin (n + 2)}
  {ia b : (KanFiber p (p.app _ e)).PtSimplex (n + 2) (fiberPoint p e)}

/-- 単位元を厳密な定数として持つ、全空間での逆元の積の充填。 -/
def totalInverse (hi : PtSimplex.MulStruct ia (a i.castSucc.castSucc) .const i) :
    PtSimplex.MulStruct (totalSimplex ia) (totalSimplex (a i.castSucc.castSucc)) .const i where
  map := hi.map ≫ fiberι p (p.app _ e)
  δ_castSucc_castSucc_map := (totalMulStruct hi).δ_castSucc_castSucc_map
  δ_succ_castSucc_map := by
    simpa only [totalSimplex_const, totalMulStruct, mapMulStruct] using
      (totalMulStruct hi).δ_succ_castSucc_map
  δ_succ_succ_map := (totalMulStruct hi).δ_succ_succ_map
  δ_map_of_lt j hj := (totalMulStruct hi).δ_map_of_lt j hj
  δ_map_of_gt j hj := (totalMulStruct hi).δ_map_of_gt j hj

/-- 相対簡約ホーンの面。基礎となる球面的簡約の面を使う。 -/
def reductionFace (hi : PtSimplex.MulStruct ia (a i.castSucc.castSucc) .const i)
    (hb : PtSimplex.MulStruct b ia (a i.succ.succ) i) (T : SphericalFiberLift p e s a)
    (j : Fin (n + 5)) : (Δ[n + 3] : SSet.{u}) ⟶ E :=
  SphericalBoundaryReduction.face
    (totalInverse hi)
    (totalMulStruct hb) (totalBoundary T) j

/-- fiber の先頭面が定数なら、全空間での簡約ホーンは互換。 -/
lemma reductionCompatible (hi : PtSimplex.MulStruct ia (a i.castSucc.castSucc) .const i)
    (hb : PtSimplex.MulStruct b ia (a i.succ.succ) i) (T : SphericalFiberLift p e s a)
    (hlower : ∀ j, j.val < i.val → a j = .const) :
    horn.IsCompatible (i := i.castSucc.succ.succ) (fun j _ ↦ reductionFace hi hb T j) := by
  apply SphericalBoundaryReduction.compatible
  intro j hj
  rw [hlower j hj, totalSimplex_const]

/-- 元の単体を置く面以外の射影は定数。 -/
lemma reductionFace_comp (hi : PtSimplex.MulStruct ia (a i.castSucc.castSucc) .const i)
    (hb : PtSimplex.MulStruct b ia (a i.succ.succ) i) (T : SphericalFiberLift p e s a)
    (j : Fin (n + 5)) :
    reductionFace hi hb T j ≫ p = if j.val = i.val + 1 then s.map else SSet.const (p.app _ e) := by
  simp only [reductionFace, SphericalBoundaryReduction.face]
  split_ifs <;> try (exfalso; omega)
  all_goals simp only [totalInverse, totalMulStruct, mapMulStruct, totalBoundary,
    totalSimplex, mapSimplex, Category.assoc, fiberι_comp, comp_const, const_comp,
    T.map_comp]

/-- 概要：球面的な一面の簡約を、底の単体を固定した相対充填で実現する。
方針：底の単体の指定退化に沿って同じ簡約ホーンを持ち上げる。
規約：i より前の面は定数。変更する二つの面は交代境界で同じ符号。
使われ方：Goerss–Jardine I §8。相対境界関係の面の逐次消去。 -/
def reduce [Fibration p]
    (hi : PtSimplex.MulStruct ia (a i.castSucc.castSucc) .const i)
    (hb : PtSimplex.MulStruct b ia (a i.succ.succ) i) (T : SphericalFiberLift p e s a)
    (hlower : ∀ j, j.val < i.val → a j = .const) :
    SphericalFiberLift p e s (SphericalBoundaryReduction.reduced a i b) := by
  have hc := reductionCompatible hi hb T hlower
  have hp (j : Fin (n + 5)) (hj : j ≠ i.castSucc.succ.succ) :
      reductionFace hi hb T j ≫ p =
        stdSimplex.δ j ≫ stdSimplex.σ i.castSucc.succ ≫ s.map := by
    rw [reductionFace_comp, SimplexFaces.degenerate_face]
    have hj' : j ≠ i.castSucc.succ.succ := hj
    congr 1
    simp only [Fin.ext_iff, Fin.val_castSucc, Fin.val_succ] at *
    have hn : j.val ≠ i.val + 1 + 1 := by
      intro h; apply hj; apply Fin.ext; simpa using h
    simp [hn]
  let hex := hc.exists_lift p (stdSimplex.σ i.castSucc.succ ≫ s.map) hp
  let φ := Classical.choose hex
  have hφ := (Classical.choose_spec hex).1
  have hcomp := (Classical.choose_spec hex).2
  refine ⟨stdSimplex.δ i.castSucc.succ.succ ≫ φ, ?_, ?_⟩
  · rw [Category.assoc, hcomp, SimplexFaces.degenerate_face, ite_eq_left (Or.inr rfl)]
  · intro j
    have he := SphericalBoundaryReduction.output_face
      (totalInverse hi)
      (totalMulStruct hb) (totalBoundary T) φ hφ j
    simp only [SphericalBoundaryReduction.reduced] at he ⊢
    split_ifs at he ⊢ <;> simpa only [totalSimplex, mapSimplex,
      RelativeMorphism.const_map, const_comp, fiberι_point] using he


end
end SphericalFiberLift
end SerrePositivity.KST.Spectra
