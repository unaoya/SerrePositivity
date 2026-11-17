module

public import SerrePositivity.AlgebraicGeometry.RectangularPerfectRowNaturality
public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechTupleFunctor

/-!
概要：同じ矩形の行の係数同型を、元の全ての単体の射を保つ図式の同型へまとめる。
方針：元のタプル複体の固定次数を評価し、検証する各成分の式を自然性へ渡す。
規約：元の構造層の appLE と交叉族の余積射の nerve を保持する。
使われ方：同じ行の交代余面微分と増大を保つ完全性の移送。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
universe u
variable {Y S : Scheme.{u}} (f : Y ⟶ S) {ι : Type} [Fintype ι] [DecidableEq ι]
variable (U : ι → Y.Opens) (p : ℕ) (hp : p.Prime)
variable (h : ∀ n : SimplexCategoryᵒᵖ,
  ∀ O, (p : ((Arrow.mk f).cechNerve.obj n).presheaf.obj O) = 0)

/-- 元の二重 Čech の縦次数 k を固定した、同じ実際の水平図式。 -/
def rectangularPerfectRowFunctor (k : ℕ) : SimplexCategory ⥤ ModuleCat.{u} ℤ where
  obj n := (schemePerfectCechTupleComplex f U p hp h n).X k
  map a := (schemePerfectCechTupleMap f U p hp h a).f k
  map_id n := by
    rw [schemePerfectCechTupleMap_id]
    rfl
  map_comp a b := by
    rw [schemePerfectCechTupleMap_comp]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- 固定した縦次数の元の写像は、矩形の交叉上の実際の appLE。 -/
theorem rectangularPerfectRowFunctor_map_apply {m n : SimplexCategory} (a : m ⟶ n)
    (k : ℕ) (x : (rectangularPerfectRowFunctor f U p hp h k).obj m)
    (q : Fin (k + 1) → Fin (n.len + 1) → ι) :
    ((rectangularPerfectRowFunctor f U p hp h k).map a).hom x q =
      frobeniusDirectLimitMap p hp
        (h (op m) (op (cechOpenIntersection (schemeCechTupleOpen f U (op m))
          (cechTupleSupport (fun r j ↦ q r (a.toOrderHom j))))))
        (h (op n) (op (cechOpenIntersection (schemeCechTupleOpen f U (op n))
          (cechTupleSupport q))))
        (((Arrow.mk f).cechNerve.map a.op).appLE
          (cechOpenIntersection (schemeCechTupleOpen f U (op m))
            (cechTupleSupport (fun r j ↦ q r (a.toOrderHom j))))
          (cechOpenIntersection (schemeCechTupleOpen f U (op n)) (cechTupleSupport q))
          (rectangularCechMap_le f U a k q)).hom
        (x (fun r j ↦ q r (a.toOrderHom j))) := by
  exact schemeStructurePerfectCechRefinedPullbackMap_apply
    ((Arrow.mk f).cechNerve.map a.op) p hp (h (op m)) (h (op n))
    (schemeCechTupleOpen f U (op m)) (schemeCechTupleOpen f U (op n))
    (fun t j ↦ t (a.toOrderHom j)) (schemeCechTupleOpen_map_le f U a.op) k x q

/-- 元の同じ交叉族の余積射の nerve の実際のΓの図式。 -/
def rectangularPerfectRowGammaFunctor (k : ℕ) : SimplexCategory ⥤ CommRingCat.{u} :=
  (Arrow.mk (Sigma.desc
    (fun b : Fin (k + 1) → ι ↦ (⨅ r, U (b r)).ι ≫ f))).cechNerve.rightOp ⋙ Scheme.Γ

set_option backward.isDefEq.respectTransparency false in
/-- 同じ各次数の環同型を、元の二つの整数加群の構造を明示して移す。 -/
def rectangularPerfectRowComponentIso (k : ℕ)
    (hN : ∀ n : SimplexCategory,
      (p : (rectangularPerfectRowGammaFunctor f U k).obj n) = 0) (n : SimplexCategory) :
    (frobeniusRingDiagram (rectangularPerfectRowGammaFunctor f U k) p hp hN).obj n ≅
      (rectangularPerfectRowFunctor f U p hp h k).obj n := by
  let e := rectangularPerfectRowEquiv f U p hp n k (hN n)
    (fun q ↦ h (op n) (op (cechOpenIntersection (schemeCechTupleOpen f U (op n))
      (cechTupleSupport q))))
  exact (e.toAddEquiv.toIntLinearEquiv
    (modM := (frobeniusRingDiagram (rectangularPerfectRowGammaFunctor f U k) p hp hN).obj n |>.isModule)
    (modM₂ := (rectangularPerfectRowFunctor f U p hp h k).obj n |>.isModule)).toModuleIso

set_option backward.isDefEq.respectTransparency false in
/-- 同じ各次数の加群同型の評価は、元の矩形の係数の同じ環同型。 -/
theorem rectangularPerfectRowComponentIso_hom_apply (k : ℕ)
    (hN : ∀ n : SimplexCategory,
      (p : (rectangularPerfectRowGammaFunctor f U k).obj n) = 0)
    (n : SimplexCategory)
    (x : (frobeniusRingDiagram (rectangularPerfectRowGammaFunctor f U k) p hp hN).obj n)
    (q : Fin (k + 1) → Fin (n.len + 1) → ι) :
    ((rectangularPerfectRowComponentIso f U p hp h k hN n).hom.hom x) q =
      rectangularPerfectRowEquiv f U p hp n k (hN n)
        (fun q ↦ h (op n) (op (cechOpenIntersection (schemeCechTupleOpen f U (op n))
          (cechTupleSupport q)))) x q := rfl

set_option backward.isDefEq.respectTransparency false in
/-- 同じ交叉族の nerve の係数と、元の実際の水平図式の自然同型。 -/
def rectangularPerfectRowFunctorIso (k : ℕ)
    (hN : ∀ n : SimplexCategory,
      (p : (rectangularPerfectRowGammaFunctor f U k).obj n) = 0) :
    frobeniusRingDiagram (rectangularPerfectRowGammaFunctor f U k) p hp hN ≅
      rectangularPerfectRowFunctor f U p hp h k := by
  refine NatIso.ofComponents
    (F := frobeniusRingDiagram (rectangularPerfectRowGammaFunctor f U k) p hp hN)
    (G := rectangularPerfectRowFunctor f U p hp h k)
    (rectangularPerfectRowComponentIso f U p hp h k hN) ?_
  intro m n a
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext q
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [rectangularPerfectRowComponentIso_hom_apply, rectangularPerfectRowFunctor_map_apply,
    rectangularPerfectRowComponentIso_hom_apply]
  exact rectangularPerfectRowEquiv_naturality f U p hp a k (hN m) (hN n)
    (fun q ↦ h (op m) (op (cechOpenIntersection (schemeCechTupleOpen f U (op m))
      (cechTupleSupport q))))
    (fun q ↦ h (op n) (op (cechOpenIntersection (schemeCechTupleOpen f U (op n))
      (cechTupleSupport q)))) x q

end SerrePositivity.AlgebraicGeometry
