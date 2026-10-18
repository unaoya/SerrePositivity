module

public import SerrePositivity.KST.DerivedGeometry.SectionLocalizationComparison

/-!
概要：tilde 層の切断の局所化比較は全ての基本開で同型。
方針：交叉を積の基本開と同定し、同じ加群の二つの局所化を比較する。
規約：自然比較そのものの同型性を証明する。
使われ方：TT §3、Bondal–van den Bergh Thm 3.1.1、Toën §3.2 の有限 Čech 各項。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory AlgebraicGeometry PrimeSpectrum
namespace SerrePositivity.KST.DerivedGeometry
variable {R : CommRingCat.{u}} (M : ModuleCat.{u} R) (a b : R)

/--
概要：D(b) から D(b) ∩ D(a) への tilde 切断の制限は a の局所化。
方針：積の基本開 D(ab) との同型で既存の反復局所化の定理を移す。
規約：同じ制限写像と R 加群構造を保持する。
使われ方：TT §3、Toën §3.2 の Čech 各項の局所化比較。
-/
lemma tilde_basicOpenIntersection_isLocalized :
    IsLocalizedModule.Away a
      (((modulesSpecToSheaf.obj (tilde M)).obj.map
        (homOfLE (inf_le_left : basicOpen b ⊓ basicOpen a ≤ basicOpen b)).op).hom) := by
  let P := (modulesSpecToSheaf.obj (tilde M)).obj
  let r := P.map (homOfLE (basicOpen_mul_le_right a b)).op
  let g := P.map (homOfLE (inf_le_left : basicOpen b ⊓ basicOpen a ≤ basicOpen b)).op
  let he : basicOpen b ⊓ basicOpen a = basicOpen (a * b) := by
    rw [basicOpen_mul, inf_comm]
  let e := P.mapIso (eqToIso he).op
  have hr : IsLocalizedModule.Away a r.hom := tilde_basicOpenRestriction_isLocalized M a b
  have hg : r ≫ e.hom = g := by
    change P.map _ ≫ P.map _ = P.map _
    rw [← P.map_comp]
    exact congrArg P.map (Subsingleton.elim _ _)
  have hi := IsLocalizedModule.of_linearEquiv (.powers a) r.hom e.toLinearEquiv
  have hi' : e.toLinearEquiv.toLinearMap ∘ₗ r.hom = g.hom :=
    congrArg ModuleCat.Hom.hom hg
  exact hi' ▸ hi

/--
概要：tilde の切断の局所化から基本開との交叉の切断への自然比較は基本開で同型。
方針：制限写像の実際の局所化性を普遍的延長の同型判定に渡す。
規約：単なる同型の存在でなく構成済みの自然比較を使う。
使われ方：TT §3、Toën §3.2 の有限基本開被覆の Čech 複体の局所化。
-/
instance sectionLocalizationComparisonAt_basicOpen_isIso :
    IsIso (sectionLocalizationComparisonAt (tilde M) a (basicOpen b)) := by
  have := tilde_basicOpenIntersection_isLocalized M a b
  exact moduleLocalizationR_lift_isIso (.powers a) _
    (basicOpenIntersection_scalarUnits (tilde M) a (basicOpen b))

end SerrePositivity.KST.DerivedGeometry
