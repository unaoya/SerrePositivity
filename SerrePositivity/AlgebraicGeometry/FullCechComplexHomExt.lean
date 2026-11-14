module

public import SerrePositivity.AlgebraicGeometry.ProjectiveCechFunctor

/-!
概要：全タプル Čech 複体の射の等式を、各次数のタプルの値で検査する。
方針：複体・加群の射・線形写像・関数の既存の外延性を一度だけ合成する。
規約：係数図式やその係数環の実装を展開しない。
使われ方：Proj の複体の自然性を、係数ごとの検証から上限内で組み立てる。
-/

@[expose] public section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u v
variable {R : Type v} [CommRing R] {ι : Type} [DecidableEq ι]
variable {D E : Finset ι ⥤ ModuleCat.{u} R}

/-- 各次数・各タプルで等しい全タプル Čech 複体の二つの射は等しい。 -/
theorem fullCechComplex_hom_ext {f g : fullCechComplex D ⟶ fullCechComplex E}
    (h : ∀ (q : ℕ) (a : FullCechCochains D (q + 1)) (t : Fin (q + 1) → ι),
      (f.f q).hom a t = (g.f q).hom a t) : f = g := by
  apply HomologicalComplex.hom_ext
  intro q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  exact funext (h q a)

end SerrePositivity.AlgebraicGeometry
