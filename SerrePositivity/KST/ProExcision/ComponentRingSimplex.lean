module
public import SerrePositivity.KST.ProExcision.ComponentRingMaps

/-!
# 成分環の実係数写像と任意の単体の成分

概要：成分環の実誘導準同型が任意の次数の成分写像と可換であることを証明する。
方針：最初の頂点への単体射に関する自然性を商写像へ移す。
規約：KST Proposition 4.14 の実係数比較。
使われ方：実同型による成分行列の単位条件の移送。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite SSet
open scoped Simplicial
variable {A B : SimplicialObject RingCat.{u}}

/-- 概要：成分環の実誘導写像は任意の次数の成分写像と可換。
方針：零次への頂点射における係数自然性を π₀ の商写像で写す。
規約：KST Proposition 4.14。使われ方：ĜL の実係数変更。 -/
lemma componentRingMap_simplex (f : A ⟶ B) (n : ℕ) (x : A.obj (op ⦋n⦌)) :
    componentRingMap f (Comparison.SimplicialRing.simplexToComponents A n x) =
      Comparison.SimplicialRing.simplexToComponents B n ((f.app (op ⦋n⦌)).hom x) := by
  have h := congrArg (fun g : A.obj (op ⦋n⦌) ⟶ B.obj (op ⦋0⦌) ↦ g.hom x)
    (f.naturality (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0).op)
  change π₀.mk (X := Comparison.ringSpace B)
      ((f.app (op ⦋0⦌)).hom ((A.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0).op).hom x)) =
    π₀.mk (X := Comparison.ringSpace B)
      ((B.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0).op).hom ((f.app (op ⦋n⦌)).hom x))
  exact congrArg (π₀.mk (X := Comparison.ringSpace B)) h

/-- 概要：成分環の実誘導同型は任意の次数の成分写像と可換。
方針：実同型の正方向の環準同型についての自然性を使う。
規約：KST Proposition 4.14。使われ方：反対環との実同型の成分への移送。 -/
lemma componentRingEquiv_simplex (e : A ≅ B) (n : ℕ) (x : A.obj (op ⦋n⦌)) :
    componentRingEquiv e (Comparison.SimplicialRing.simplexToComponents A n x) =
      Comparison.SimplicialRing.simplexToComponents B n ((e.hom.app (op ⦋n⦌)).hom x) :=
  componentRingMap_simplex e.hom n x

end SerrePositivity.KST.ProExcision
