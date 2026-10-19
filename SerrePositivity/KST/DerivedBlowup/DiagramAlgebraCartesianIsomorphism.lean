module

public import SerrePositivity.KST.DerivedBlowup.DiagramAlgebraCartesianCondition

/-!
概要：KST v4 §3.1（pp.11–14）の正規表示の cartesian 条件の同型不変性。
方針：canonical な係数拡大比較の自然性で同型に沿う共役を計算する。
規約：指定比較射の可逆性を移す。任意の同型による代用はしない。
使われ方：一般の係数図式の cartesian perfect 部分圏への同値の制限。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.DerivedBlowup
open CategoryTheory DifferentialGraded
variable {R : Type u} [CommRing R] {J : Type v} [Preorder J] [DecidableLE J]
variable (F : J ⥤ Mon (Complex R)) [Small.{u} (DiagramModuleCoefficientObject F)]

/-- 概要：正規表示の canonical な cartesian 条件は同型で不変。
方針：指定比較の自然性から同型による共役として書く。
規約：KST §3.1。使われ方：表示同値を対象条件へ制限する。 -/
instance diagramAlgebraCartesianClosedUnderIso :
    (diagramAlgebraCartesian F).IsClosedUnderIsomorphisms where
  of_iso e hX i j h := by
    let L := diagramAlgebraDerivedEvaluation F i ⋙ diagramAlgebraDerivedExtension F h
    let V := diagramAlgebraDerivedEvaluation F j
    let τ := diagramAlgebraDerivedExtensionNatTrans F h
    have hn := τ.naturality e.hom
    have he : τ.app _ = L.map e.inv ≫ τ.app _ ≫ V.map e.hom := by
      rw [← hn, ← Category.assoc, ← L.map_comp, e.inv_hom_id,
        L.map_id, Category.id_comp]
    change IsIso (τ.app _)
    rw [he]
    have : IsIso (τ.app _) := hX i j h
    infer_instance

/-- 概要：正規表示の cartesian perfect 条件は同型で不変。
方針：cartesian 性と局所 perfect 性の同型不変性を組み合わせる。
規約：KST §3.1。使われ方：対象条件により指定導来同値を制限する。 -/
instance diagramAlgebraCartesianPerfectClosedUnderIso :
    (diagramAlgebraCartesianPerfect F).IsClosedUnderIsomorphisms where
  of_iso e hX := ⟨(diagramAlgebraCartesian F).prop_of_iso e hX.1,
    (diagramAlgebraLocallyPerfect F).prop_of_iso e hX.2⟩

end SerrePositivity.KST.DerivedBlowup
