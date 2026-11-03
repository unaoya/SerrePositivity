module
public import SerrePositivity.KST.SConstruction.DGRestrictedYoneda
public import SerrePositivity.DifferentialGraded.Module.ConeConstruction

/-! # 元の二つの dg 関手に沿う Hom gluing 双加群
概要：Hom_E(p(c),q(d)) を全次数の左右作用を持つ実双加群として構成する。
方針：標的の Small 性を使わない制限 Yoneda に q を前合成し、元の Hom 作用を回収する。
規約：双加群は第一変数反変・第二変数共変。使われ方：Perf 四角形の標準対角。
-/
@[expose] public section
noncomputable section
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Opposite
open SerrePositivity.DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (E : Type z) [DGCategory R E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)

/-- 元の二関手を保つ、Hom_E(p(c),q(d)) の実双加群。 -/
def dgHomGluingBimodule : Bimodule R C D := q.comp (dgRestrictedYoneda R C E p)

/-- 同じ実双加群の値は、元の標的内の全 Hom 複体そのもの。 -/
lemma dgHomGluingBimodule_value (c : C) (d : D) :
    (dgHomGluingBimodule R C D E p q).value c d = homObject R E (p.obj c) (q.obj d) := rfl

/-- 同じ双加群の右作用は、元の p の Hom 像による前合成そのもの。 -/
lemma dgHomGluingBimodule_rightAction (d : D) {x y : C} {n i m : ℤ}
    (f : GradedHom R x y n) (v : GradedHom R (p.obj y) (q.obj d) i) (hm : i + n = m) :
    moduleAction R ((dgHomGluingBimodule R C D E p q).rightAt d)
      (x := op y) (y := op x) f v hm =
      forward R ((p.map x y).f n f) v (by omega) := rfl

/-- 同じ双加群の左全 Hom 作用は、元の q と標的の共変代表作用を回収する。 -/
lemma dgHomGluingBimodule_leftAt_map (c : C) (d d' : D) :
    ((dgHomGluingBimodule R C D E p q).leftAt c).map d d' =
      q.map d d' ≫ (leftRepresentable R (p.obj c)).map (q.obj d) (q.obj d') := by
  change (q.map d d' ≫ (dgRestrictedYoneda R C E p).map (q.obj d) (q.obj d')) ≫
    moduleHomπ R C _ _ c = _
  exact (Category.assoc _ _ _).trans
    (congrArg (fun k => q.map d d' ≫ k)
      (dgRestrictedYoneda_map_π R C E p (q.obj d) (q.obj d') c))

/-- 同じ双加群の左作用は、元の q の Hom 像による符号付き後合成。 -/
lemma dgHomGluingBimodule_leftAction (c : C) {d d' : D} {n i m : ℤ}
    (g : GradedHom R d d' n) (v : GradedHom R (p.obj c) (q.obj d) i) (hm : i + n = m) :
    leftAction R ((dgHomGluingBimodule R C D E p q).leftAt c) g v hm =
      (n * i).negOnePow • forward R v ((q.map d d').f n g) hm := by
  change ((((dgHomGluingBimodule R C D E p q).leftAt c).map d d').f n g).v i m hm v = _
  rw [dgHomGluingBimodule_leftAt_map]
  exact leftRepresentable_action R (p.obj c) (q.obj d) (q.obj d')
    ((q.map d d').f n g) v hm

end SerrePositivity.KST.SConstruction
