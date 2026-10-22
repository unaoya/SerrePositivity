module
public import SerrePositivity.KST.SConstruction.PointedSOAExInfinityComparison
public import SerrePositivity.KST.Spectra.PointedComponentIsomorphism

/-! # 元の点つき Kan 置換による成分等号の保存
概要：同じ元の SOA 置換は、基点固定成分の等号を保存する。
方針：豊穣な Ex∞ の作用へ移し、元の前向き比較の全基点 π 同型で反映する。
規約：SOA の豊穣性は要求しない。使われ方：実 Perf 評価と既存 BF K の比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet Spectra
open Spectra.PointedMapping
open scoped Simplicial

/-- 同じ Ex∞ の全 Hom 作用は、通常射の点つき頂点を回収する。 -/
lemma exInfinityPointedKanEnrichedFunctor_vertex {X Y : PointedSSetObject.{u}}
    (f : X ⟶ Y) :
    (exInfinityPointedKanEnrichedFunctor.map X Y).app (Opposite.op ⦋0⦌)
        (familyVertex (show X.obj ⟶ Y.obj from f)) =
      familyVertex (exInfinityPointedKanMap f).hom := by
  have h := congrArg (fun q => q.app (Opposite.op ⦋0⦌) PUnit.unit)
    (exInfinityPointedKanEnrichedFunctor_hom f)
  rw [familyVertex_eq_pointedHomVertex]
  exact h.trans (familyVertex_eq_pointedHomVertex _).symm

/-- 同じ元の点つき射の成分等号を、同じ Ex∞ の実際の射へ送る。 -/
lemma exInfinityPointedKanMap_component {X Y : PointedSSetObject.{u}} {f g : X ⟶ Y}
    (h : componentOf (show X.obj ⟶ Y.obj from f) = componentOf g) :
    componentOf (exInfinityPointedKanMap f).hom =
      componentOf (exInfinityPointedKanMap g).hom := by
  let p : (PointedObject.basedHom X.obj Y.obj).right ⟶
      (PointedObject.basedHom (exInfinityPointedKanEnrichedFunctor.obj X).obj
        (exInfinityPointedKanEnrichedFunctor.obj Y).obj).right :=
    exInfinityPointedEnrichedFunctor.map X Y
  have hf : p.app (Opposite.op ⦋0⦌) (familyVertex f) =
      familyVertex (exInfinityPointedKanMap f).hom :=
    exInfinityPointedKanEnrichedFunctor_vertex f
  have hg : p.app (Opposite.op ⦋0⦌) (familyVertex g) =
      familyVertex (exInfinityPointedKanMap g).hom :=
    exInfinityPointedKanEnrichedFunctor_vertex g
  have hh := congrArg (mapπ₀ p) h
  simpa only [componentOf, mapπ₀_mk, hf, hg] using hh

/-- 元の SOA Kan 置換は、同じ点つき射の基点固定成分等号を保存する。 -/
lemma pointedKanReplacement_map_component {X Y : PointedSimplicialSet.{u}}
    {f g : X ⟶ Y} (h : componentOf f = componentOf g) :
    componentOf (PointedKanReplacement.map f) =
      componentOf (PointedKanReplacement.map g) := by
  let X' : PointedSSetObject.{u} := ⟨X⟩
  let Y' : PointedSSetObject.{u} := ⟨Y⟩
  have he := exInfinityPointedKanMap_component (X := X') (Y := Y') (f := f) (g := g) h
  apply componentOf_cancel_post_piIsomorphism (pointedSOAExInfinityComparison Y')
    (pointedSOAExInfinityComparison_piIsomorphism Y')
  exact (pointedSOAExInfinityComparison_naturality_component (X := X') (Y := Y') f).symm.trans
    ((componentOf_comp_left he (pointedSOAExInfinityComparison X')).trans
      (pointedSOAExInfinityComparison_naturality_component (X := X') (Y := Y') g))

end SerrePositivity.KST.SConstruction
