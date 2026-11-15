module

public import SerrePositivity.BhattScholze.Semiperfectoid.Quasiregular.RootRelationEnvelopeFaithful
public import SerrePositivity.BhattScholze.Semiperfectoid.Quasiregular.RootFamilyReindex
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.FiniteQuotientComplete
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionFunctor
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionLinearMap

/-!
# 有限 T と宇宙を持ち上げた根付き表示の比較

## 概要
Fin r の有限模型を、ULift 添字の全関係を割って実 H⁰ 完備化する drafts の模型と比較する。
## 方針
添字変更が係数と各段の根を保つことから、関係イデアル・商・実完備化へ同型を移す。
## 規約
BS 著者版 Proposition 7.10。全ての根を殺すイデアルは使わず、第零段だけに関係を置く。
## 使われ方
drafts の regularSemiperfectoid の具体環との照合。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Semiperfectoid
open _root_.SerrePositivity.DerivedCompletion _root_.SerrePositivity.BhattScholze.Andre
set_option backward.isDefEq.respectTransparency false
variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] {r : ℕ} (f : Fin r → R)

/-- 小さい添字から持ち上げた添字への根付き基底の同型。 -/
def rootFamilyFiniteLiftEquiv :
    rootFamilyBase p R (Fin r) ≃+* rootFamilyBase p R (ULift.{u} (Fin r)) :=
  rootFamilyBaseReindex p R (Equiv.ulift.symm : Fin r ≃ ULift.{u} (Fin r))

/-- 根付き基底の添字同型は、係数環からの構造射を保つ。 -/
theorem rootFamilyBaseReindex_coefficient {J : Type} {K : Type u} (e : J ≃ K) (x : R) :
    rootFamilyBaseReindex p R e (algebraMap R (rootFamilyBase p R J) x) =
      algebraMap R (rootFamilyBase p R K) x := by
  change rootFamilyBaseReindex p R e
    (rootFamilyUnit p R J (AddMonoidAlgebra.single 0 x)) = _
  rw [rootFamilyBaseReindex_unit]
  change rootFamilyUnit p R K (rootFamilyRawReindex p R e (AddMonoidAlgebra.single 0 x)) = _
  rw [rootFamilyRawReindex, AddMonoidAlgebra.mapDomainRingEquiv_single, map_zero]
  rfl

/-- drafts と同じ ULift 添字の初期根の関係。 -/
def rootLiftRelation (i : ULift.{u} (Fin r)) : rootFamilyBase p R (ULift.{u} (Fin r)) :=
  rootFamilyVariable p R (ULift.{u} (Fin r)) i 0 - algebraMap R _ (f i.down)

/-- ULift 添字の全初期関係が生成するイデアル。 -/
def rootLiftRelationIdeal : Ideal (rootFamilyBase p R (ULift.{u} (Fin r))) :=
  Ideal.span (Set.range (rootLiftRelation p R f))

/-- ULift 添字の通常の有限関係商。 -/
abbrev rootLiftRelationQuotient :=
  rootFamilyBase p R (ULift.{u} (Fin r)) ⧸ rootLiftRelationIdeal p R f

/-- drafts の regularSemiperfectoid と同じ、関係商の実 H⁰ p 完備化。 -/
abbrev rootLiftRelationCompletion :=
  PrincipalCompletionH0 (rootLiftRelationQuotient p R f) (p : rootLiftRelationQuotient p R f)

/-- ULift 関係商の実完備化には、既存の主元完備化の環構造を使う。 -/
instance rootLiftRelationCompletionCommRing : CommRing (rootLiftRelationCompletion p R f) :=
  principalCompletionCommRing _ _

/-- 添字の同型は、完備な基底上の有限関係列を対応する初期根の関係へ送る。 -/
theorem rootFamilyFiniteLiftEquiv_relation (i : Fin r) :
    rootFamilyFiniteLiftEquiv p R (rootRelationSequence p R f i) =
      rootLiftRelation p R f (ULift.up i) := by
  rw [rootRelationSequence_apply, map_sub]
  change rootFamilyBaseReindex p R _ (rootFamilyVariable p R (Fin r) i 0) -
    rootFamilyBaseReindex p R _ (algebraMap R _ (f i)) = _
  rw [rootFamilyBaseReindex_variable, rootFamilyBaseReindex_coefficient]
  rfl

/-- ULift の関係は、小さい Fin r を走らせた関係と同じイデアルを生成する。 -/
theorem rootLiftRelationIdeal_eq : rootLiftRelationIdeal p R f =
    Ideal.span (Set.range (fun i : Fin r => rootLiftRelation p R f (ULift.up i))) := by
  apply congrArg Ideal.span
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i.down, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨ULift.up i, rfl⟩

/-- 基底の添字変更は、実際の有限関係イデアルを保つ。 -/
theorem rootFamilyFiniteLiftEquiv_map_ideal :
    (rootRelationBaseIdeal p R f).map (rootFamilyFiniteLiftEquiv p R).toRingHom =
      rootLiftRelationIdeal p R f := by
  rw [rootRelationBaseIdeal_eq, Ideal.map_span, ← Set.range_comp, rootLiftRelationIdeal_eq]
  congr 1
  congr 1
  funext i
  exact rootFamilyFiniteLiftEquiv_relation p R f i

/-- 通常の有限関係商の添字比較。 -/
def rootRelationLiftQuotientEquiv : rootRelationQuotient p R f ≃+* rootLiftRelationQuotient p R f :=
  Ideal.quotientEquiv _ _ (rootFamilyFiniteLiftEquiv p R)
    (rootFamilyFiniteLiftEquiv_map_ideal p R f).symm

/-- 通常商の比較は、基底からの商単位を保つ。 -/
theorem rootRelationLiftQuotientEquiv_mk (x : rootFamilyBase p R (Fin r)) :
    rootRelationLiftQuotientEquiv p R f (rootRelationQuotientUnit p R f x) =
      Ideal.Quotient.mk _ (rootFamilyFiniteLiftEquiv p R x) := by
  rfl

/-- 通常の有限 T と、drafts の ULift 関係商の実完備化との同型。 -/
def rootRelationLiftCompletionEquiv : rootRelationQuotient p R f ≃+* rootLiftRelationCompletion p R f := by
  let T := rootRelationQuotient p R f
  let L := rootLiftRelationQuotient p R f
  letI := principalCompletionCommRing T (p : T)
  letI := principalCompletionCommRing L (p : L)
  let e0 := principalCompletionEquivOfComplete T (p : T) (rootRelationQuotient_complete p R f)
  let e1 := principalCompletionRingEquiv (rootRelationLiftQuotientEquiv p R f)
    (p : T) (p : L) (map_natCast _ p)
  exact e0.symm.trans e1

/-- 実完備化までの添字比較は、元の基底の代表元を保つ。 -/
theorem rootRelationLiftCompletionEquiv_unit (x : rootFamilyBase p R (Fin r)) :
    rootRelationLiftCompletionEquiv p R f (rootRelationQuotientUnit p R f x) =
      principalCompletionUnitRingHom (rootLiftRelationQuotient p R f) (p : rootLiftRelationQuotient p R f)
        (Ideal.Quotient.mk _ (rootFamilyFiniteLiftEquiv p R x)) := by
  unfold rootRelationLiftCompletionEquiv
  change principalCompletionRingEquiv (rootRelationLiftQuotientEquiv p R f)
    (p : rootRelationQuotient p R f) (p : rootLiftRelationQuotient p R f) (map_natCast _ p)
    (principalCompletionUnitRingHom (rootRelationQuotient p R f) _ (rootRelationQuotientUnit p R f x)) =
    principalCompletionUnitRingHom (rootLiftRelationQuotient p R f) _
      (Ideal.Quotient.mk _ (rootFamilyFiniteLiftEquiv p R x))
  rw [principalCompletionRingEquiv_unit, rootRelationLiftQuotientEquiv_mk]

end SerrePositivity.BhattScholze.Semiperfectoid
