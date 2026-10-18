module

public import SerrePositivity.KST.DerivedBlowup.DiagramCartesianCondition
public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapDerivedNaturality

/-!
概要：KST §3.1 の指定 cartesian 条件の同型不変性。
方針：指定導来係数拡大比較の自然性によって同型に沿う比較射を共役で表す。
規約：局所 perfect 性と合わせた性質にも同型不変性を装備する。
使われ方：射影的代表を選び直しても cartesian・perfect 条件を保つことの保証。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory
open DifferentialGraded

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I]

/-- 概要：指定 cartesian 条件は導来図式加群の同型で不変。
方針：自然性から比較射を同型と元の比較射の合成で表す。
規約：KST §3.1、対象間の任意の同型の存在で比較射を置き換えない。
使われ方：全図式の半自由・射影的置換への条件の移送。 -/
instance diagramCartesianClosedUnderIso (a : I → R) :
    (diagramCartesian R a).IsClosedUnderIsomorphisms where
  of_iso e hX T U h := by
    let F := finiteOverlapDerivedModuleEvaluation R a T ⋙
      finiteOverlapDerivedTransitionExtension R a h
    let G := finiteOverlapDerivedModuleEvaluation R a U
    let τ := finiteOverlapDerivedExtensionNatTrans R a h
    have hn := τ.naturality e.hom
    have he : τ.app _ = F.map e.inv ≫ τ.app _ ≫ G.map e.hom := by
      rw [← hn, ← Category.assoc, ← F.map_comp, e.inv_hom_id,
        F.map_id, Category.id_comp]
    change IsIso (τ.app _)
    rw [he]
    have : IsIso (τ.app _) := hX T U h
    infer_instance

/-- 概要：指定 cartesian 性と局所 perfect 性の連言は同型で不変。
方針：二つの構成済みの同型不変性をそれぞれ使う。
規約：KST §3.1。使われ方：Perf 候補への射影的模型の比較の制限。 -/
instance diagramCartesianPerfectClosedUnderIso (a : I → R) :
    (diagramCartesianPerfect R a).IsClosedUnderIsomorphisms where
  of_iso e hX := ⟨(diagramCartesian R a).prop_of_iso e hX.1,
    (diagramLocallyPerfect R a).prop_of_iso e hX.2⟩

end SerrePositivity.KST.DerivedBlowup
