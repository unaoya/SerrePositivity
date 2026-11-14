module

public import SerrePositivity.EInfinity.PowerOperation.MayProbeEvaluation
public import SerrePositivity.EInfinity.PowerOperation.MaySphereHomotopy

/-!
# May の指定 D_i のホモロジー類と代表元独立性

May, Proposition 2.3 の代表元独立性。
閉性と厳密自然性を、既存の自由 cofibrant probe と sphere 射の鎖ホモトピーに適用する。
新しい同変ホモトピーや軌道・Tate のスペクトル模型は用いない。
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
open SerrePositivity.EInfinity.BarrattEccles
variable {k : Type u} [CommRing k]
variable (p : ℕ) [NeZero p] [Fact p.Prime] [CharP k p]
variable (X : (operad k).Algebra)

/-- 同じ指定 D_s の閉元の実ホモロジー類。 -/
def mayDClass (s : ℕ) (q : ℤ) (a : MayClosed X.carrier q) :
    X.carrier.homology (-(s : ℤ) + mayRepeatedDegree q p) :=
  mayClosedClass X.carrier _ (mayDClosed X p s q a)

lemma mayDClass_naturality {Y : (operad k).Algebra} (f : X ⟶ Y)
    (s : ℕ) (q : ℤ) (a : MayClosed X.carrier q) :
    homologyMap f.hom (-(s : ℤ) + mayRepeatedDegree q p) (mayDClass p X s q a) =
      mayDClass p Y s q (mayClosedMap f.hom q a) := by
  rw [mayDClass, mayClosedClass_naturality, mayDClosed_naturality]
  rfl

/-- 同じホモロジー類を表す入力には、同じ D_s のホモロジー類が対応する。 -/
lemma mayDClass_independent (s : ℕ) (q : ℤ) (a b : MayClosed X.carrier q)
    (hab : mayClosedClass X.carrier q a = mayClosedClass X.carrier q b) :
    mayDClass p X s q a = mayDClass p X s q b := by
  let S := complexSphere k q
  let e : MayClosed S q := complexSphereHomEquiv k S q (𝟙 S)
  let z := mayProbeFreeCycle S q e
  have H := maySphereHomotopy X.carrier q a b hab
  have hm := mayProbeLiftHom_homology_eq X H (-(s : ℤ) + mayRepeatedDegree q p)
  have he := congrArg
    (fun h : ((freeProbeFunctor k).obj S).carrier.homology
        (-(s : ℤ) + mayRepeatedDegree q p) ⟶
        X.carrier.homology (-(s : ℤ) + mayRepeatedDegree q p) =>
      h (mayDClass p ((freeProbeFunctor k).obj S) s q z)) hm
  rw [mayDClass_naturality, mayDClass_naturality] at he
  change mayDClass p X s q
      (mayClosedMap (mayProbeLiftHom X ((complexSphereHomEquiv k X.carrier q).symm a)).hom q
        (mayProbeFreeCycle S q e)) =
    mayDClass p X s q
      (mayClosedMap (mayProbeLiftHom X ((complexSphereHomEquiv k X.carrier q).symm b)).hom q
        (mayProbeFreeCycle S q e)) at he
  rw [mayProbeFreeCycle_evaluation, mayProbeFreeCycle_evaluation] at he
  dsimp only [e, S] at he
  rw [maySphereGenerator_map, maySphereGenerator_map] at he
  exact he

end SerrePositivity.EInfinity.PowerOperation
