module
public import SerrePositivity.KST.SConstruction.DGSmallPerfectEnvelopeFunctorLift
public import SerrePositivity.KST.SConstruction.DGFullClosedMapLift

/-!
概要：元実像を保持する共通小模型への制限は同じ全 Hom 自然な閉比較を保持する。
方針：閉射を perfect 模型と指定実像模型へ二段で明示的に持ち上げる。
規約：元閉射を同型な代表へ選び直さない。使われ方：LT 逆回転の全自然性の小模型への輸送。
-/
@[expose] public section
noncomputable section
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E] [Small.{u} E]
  (J : Type w) (X : J → PerfectDGModule R E) {P : Type z} [DGCategory R P]
  (F G : DGFunctor R P (PerfectDGModule R E)) (i j : P → J)
  (hF : ∀ a, X (i a) = F.obj a) (hG : ∀ a, X (j a) = G.obj a)
  (a : ∀ x, ForgetEnrichment.of (Complex R) (F.obj x).val ⟶
    ForgetEnrichment.of (Complex R) (G.obj x).val)

/-- 概要：元実加群の閉射を同じ二実像小模型の閉射として保持する。
方針：二つの充満 dg 部分圏へ元閉射を明示的に持ち上げる。
規約：同じ元射を保持。使われ方：全 Hom 自然性の所属圏を固定する。 -/
def dgSmallPerfectEnvelopeComparisonMap (x : P) :
    ForgetEnrichment.of (Complex R)
      ((dgSmallPerfectEnvelopeFunctorLift R E J X F i hF).obj x) ⟶
    ForgetEnrichment.of (Complex R)
      ((dgSmallPerfectEnvelopeFunctorLift R E J X G j hG).obj x) :=
  dgFullClosedMapLift R (PerfectDGModule R E) (dgSmallPerfectEnvelopeObjects R E J X)
    ((dgSmallPerfectEnvelopeFunctorLift R E J X F i hF).obj x)
    ((dgSmallPerfectEnvelopeFunctorLift R E J X G j hG).obj x)
    (dgPerfectClosedMapLift R E (F.obj x) (G.obj x) (a x))

/-- 概要：元全 Hom 自然な実閉比較は同じ共通小模型でも全 Hom 自然。
方針：二段の充満部分圏の前後合成回収と同じ元自然性を接続する。
規約：元閉射とその全次数自然性を保持。使われ方：長い実 cone 関手を展開しない輸送。 -/
lemma dgSmallPerfectEnvelopeFunctorLift_comparison_naturality
    (h : ∀ x y, F.map x y ≫
        eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (F.obj x).val) (a y) =
      G.map x y ≫ eHomWhiskerRight (Complex R) (a x)
        (ForgetEnrichment.of (Complex R) (G.obj y).val)) (x y : P) :
    (dgSmallPerfectEnvelopeFunctorLift R E J X F i hF).map x y ≫
      eHomWhiskerLeft (Complex R)
        (ForgetEnrichment.of (Complex R)
          ((dgSmallPerfectEnvelopeFunctorLift R E J X F i hF).obj x))
        (dgSmallPerfectEnvelopeComparisonMap R E J X F G i j hF hG a y) =
    (dgSmallPerfectEnvelopeFunctorLift R E J X G j hG).map x y ≫
      eHomWhiskerRight (Complex R)
        (dgSmallPerfectEnvelopeComparisonMap R E J X F G i j hF hG a x)
        (ForgetEnrichment.of (Complex R)
          ((dgSmallPerfectEnvelopeFunctorLift R E J X G j hG).obj y)) := by
  have hl := (dgFullClosedMapLift_whiskerLeft R (PerfectDGModule R E)
    (dgSmallPerfectEnvelopeObjects R E J X)
    ((dgSmallPerfectEnvelopeFunctorLift R E J X F i hF).obj y)
    ((dgSmallPerfectEnvelopeFunctorLift R E J X G j hG).obj y)
    (dgPerfectClosedMapLift R E (F.obj y) (G.obj y) (a y))
    ((dgSmallPerfectEnvelopeFunctorLift R E J X F i hF).obj x)).trans
      (dgPerfectClosedMapLift_whiskerLeft R E (F.obj y) (G.obj y) (F.obj x) (a y))
  have hr := (dgFullClosedMapLift_whiskerRight R (PerfectDGModule R E)
    (dgSmallPerfectEnvelopeObjects R E J X)
    ((dgSmallPerfectEnvelopeFunctorLift R E J X F i hF).obj x)
    ((dgSmallPerfectEnvelopeFunctorLift R E J X G j hG).obj x)
    (dgPerfectClosedMapLift R E (F.obj x) (G.obj x) (a x))
    ((dgSmallPerfectEnvelopeFunctorLift R E J X G j hG).obj y)).trans
      (dgPerfectClosedMapLift_whiskerRight R E (F.obj x) (G.obj x) (G.obj y) (a x))
  exact (congrArg₂ (fun k l => k ≫ l)
    (dgSmallPerfectEnvelopeFunctorLift_map R E J X F i hF x y) hl).trans
      ((h x y).trans (congrArg₂ (fun k l => k ≫ l)
        (dgSmallPerfectEnvelopeFunctorLift_map R E J X G j hG x y) hr).symm)
end SerrePositivity.KST.SConstruction
