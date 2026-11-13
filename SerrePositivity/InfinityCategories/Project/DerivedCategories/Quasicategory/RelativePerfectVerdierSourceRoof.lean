module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.RelativeVerdierDiagramComparison
public import SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierImageTransport
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierStrict

/-!
概要：完備化付き長方形の始域を、元入力への増大屋根と指定 ν 同値で回収する。
方針：同じ共通始域からの二本の実辺と、ν 像の指定同値との可換式を保持する。
規約：S 内の逆増大や頂点等号を要求しない。屋根の実在は別途供給する。
使われ方：K-S• の元始域回収と、指定全境界比較を持つ実相対長方形。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierSourceRoof
end SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierSourceRoof
namespace SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierRectangle
end SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierRectangle
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory
open _root_.SerrePositivity.KST.LocalizingInvariants

/-- 元入力と長方形の始域への実屋根。指定同値は同じ二本の ν 像を照合する。 -/
structure RelativePerfectVerdierSourceRoof {S : SSet.{u + 1}}
    (ν : S ⟶ perfectStableInfinity.{u}) (original actual : S _⦋0⦌) where
  common : S _⦋0⦌
  augmentation : Truncated.Edge (X := (truncation 2).obj S) common original
  comparison : Truncated.Edge (X := (truncation 2).obj S) common actual
  augmentation_invertible : IsIso ((hoFunctor.map ν).toFunctor.map
    (Truncated.HomotopyCategory.homMk augmentation))
  comparison_invertible : IsIso ((hoFunctor.map ν).toFunctor.map
    (Truncated.HomotopyCategory.homMk comparison))
  image : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (ν.app _ original) (ν.app _ actual)
  triangle : (hoFunctor.map ν).toFunctor.map
      (Truncated.HomotopyCategory.homMk augmentation) ≫ image.hom =
    (hoFunctor.map ν).toFunctor.map (Truncated.HomotopyCategory.homMk comparison)

namespace RelativePerfectVerdierSourceRoof

variable {S : SSet.{u + 1}} {ν : S ⟶ perfectStableInfinity.{u}}
  {original actual : S _⦋0⦌}

/-- 旧頂点等号は、同じ頂点での恒等屋根による特殊化。 -/
def ofEq (h : original = actual) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierSourceRoof ν original actual := by
  subst actual
  refine ⟨original, Truncated.Edge.id (X := (truncation 2).obj S) original,
    Truncated.Edge.id (X := (truncation 2).obj S) original, ?_, ?_,
    Iso.refl _, ?_⟩
  · simp only [Truncated.HomotopyCategory.homMk_id]
    infer_instance
  · simp only [Truncated.HomotopyCategory.homMk_id]
    infer_instance
  · exact Category.comp_id _

/-- 指定した ν 同値を、同じ Cat^perf 不変量で写した始域同値。 -/
def valueIso (r : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierSourceRoof ν original actual)
    (E : perfectStableInfinity.{u} ⟶ _root_.SerrePositivity.KST.Spectra.Sp.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((ν ≫ E).app _ original) ((ν ≫ E).app _ actual) := r.image.map E

/-- 元の増大・核比較との可換式は値へ写しても同じもの。 -/
lemma valueIso_triangle (r : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierSourceRoof ν original actual)
    (E : perfectStableInfinity.{u} ⟶ _root_.SerrePositivity.KST.Spectra.Sp.{u}) :
    (hoFunctor.map E).toFunctor.map ((hoFunctor.map ν).toFunctor.map
      (Truncated.HomotopyCategory.homMk r.augmentation)) ≫ (r.valueIso E).hom =
    (hoFunctor.map E).toFunctor.map ((hoFunctor.map ν).toFunctor.map
      (Truncated.HomotopyCategory.homMk r.comparison)) := by
  change (hoFunctor.map E).toFunctor.map _ ≫ (hoFunctor.map E).toFunctor.map r.image.hom = _
  rw [← Functor.map_comp, r.triangle]

/-- 旧頂点等号を入れた値の比較は、元の等号輸送そのもの。 -/
@[simp] lemma valueIso_ofEq (h : original = actual)
    (E : perfectStableInfinity.{u} ⟶ _root_.SerrePositivity.KST.Spectra.Sp.{u}) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierSourceRoof.ofEq (ν := ν) h).valueIso E =
      eqToIso (congrArg (fun x => HomotopyCategory.mk ((ν ≫ E).app _ x)) h) := by
  subst actual
  apply Iso.ext
  simp [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierSourceRoof.valueIso, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierSourceRoof.ofEq, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map]

/-- 認証に使う別の S 代表を要求せず、実長方形の始域屋根と全 ν 比較を接続する。 -/
def rectangleValueIso_of_imageIso
    {G : (Δ[2] ⊗ Δ[1] : SSet.{u + 1}) ⟶ S}
    {F : (Δ[2] ⊗ Δ[1] : SSet.{u + 1}) ⟶ perfectStableInfinity.{u}}
    (b : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierRectangleBoundaryIso (G ≫ ν) F)
    (e : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierRectangleDiagramIso (G ≫ ν) F b)
    (r : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierSourceRoof ν original
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex ((β_ _ _).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare G 2) 0 0))
    (E : perfectStableInfinity.{u} ⟶ _root_.SerrePositivity.KST.Spectra.Sp.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((ν ≫ E).app _ original)
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (((β_ _ _).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 2) ≫ E) 0 0) := by
  let c := (β_ (Δ[1] : SSet.{u + 1}) Δ[1]).hom ≫
    (stdSimplex.δ (2 : Fin 3) ▷ (Δ[1] : SSet.{u + 1}))
  exact r.valueIso E ≪≫
    (((e.comparison.precomp c).postcomp E).toNatIso.app
      (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (𝟙 (Δ[1] ⊗ Δ[1] : SSet.{u + 1})) 0 0)))

/-- 始域回収は全長方形比較の同じ成分を使い、元の屋根の可換式を保持する。 -/
lemma rectangleValueIso_of_imageIso_triangle
    {G : (Δ[2] ⊗ Δ[1] : SSet.{u + 1}) ⟶ S}
    {F : (Δ[2] ⊗ Δ[1] : SSet.{u + 1}) ⟶ perfectStableInfinity.{u}}
    (b : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierRectangleBoundaryIso (G ≫ ν) F)
    (e : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierRectangleDiagramIso (G ≫ ν) F b)
    (r : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierSourceRoof ν original
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex ((β_ _ _).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare G 2) 0 0))
    (E : perfectStableInfinity.{u} ⟶ _root_.SerrePositivity.KST.Spectra.Sp.{u}) :
    (hoFunctor.map E).toFunctor.map ((hoFunctor.map ν).toFunctor.map
      (Truncated.HomotopyCategory.homMk r.augmentation)) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierSourceRoof.rectangleValueIso_of_imageIso b e r E).hom =
    (hoFunctor.map E).toFunctor.map ((hoFunctor.map ν).toFunctor.map
      (Truncated.HomotopyCategory.homMk r.comparison)) ≫
        (((e.comparison.precomp ((β_ (Δ[1] : SSet.{u + 1}) Δ[1]).hom ≫
          (stdSimplex.δ (2 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})))).postcomp E).toNatIso.app
            (HomotopyCategory.mk
              (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (𝟙 (Δ[1] ⊗ Δ[1] : SSet.{u + 1})) 0 0))).hom := by
  change _ ≫ ((r.valueIso E).hom ≫ _) = _
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun f => f ≫ _) (r.valueIso_triangle E))

end RelativePerfectVerdierSourceRoof

namespace RelativePerfectVerdierRectangle

variable {S : SSet.{u + 1}} {ν : S ⟶ perfectStableInfinity.{u}}
  (d : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierRectangle ν)

/-- 旧厳密版の始域頂点等号を、同じ長方形の恒等屋根として受ける。 -/
def sourceRoofOfEq {original : S _⦋0⦌}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex ((β_ _ _).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare d.diagram 2) 0 0 = original) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierSourceRoof ν original
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex ((β_ _ _).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare d.diagram 2) 0 0) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierSourceRoof.ofEq h.symm

/-- 実長方形を変えず、左上の値を元入力の値へ指定屋根で照合する。 -/
def sourceValueIso {original : S _⦋0⦌}
    (r : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierSourceRoof ν original
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex ((β_ _ _).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare d.diagram 2) 0 0))
    (E : perfectStableInfinity.{u} ⟶ _root_.SerrePositivity.KST.Spectra.Sp.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((ν ≫ E).app _ original)
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (((β_ _ _).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare d.diagram 2) ≫ ν ≫ E) 0 0) :=
  r.valueIso E

/-- 指定三境界・上下二単体を保つ全 ν 比較と、元入力の指定屋根を同時に使う。
同型は全長方形の比較の同じ左上成分を用い、始域で別の比較を選び直さない。 -/
def sourceValueIso_of_imageIso {F : (Δ[2] ⊗ Δ[1] : SSet.{u + 1}) ⟶ S}
    (b : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierRectangleBoundaryIso (d.diagram ≫ ν) (F ≫ ν))
    (e : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierRectangleDiagramIso (d.diagram ≫ ν) (F ≫ ν) b)
    {original : S _⦋0⦌}
    (r : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierSourceRoof ν original
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex ((β_ _ _).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare d.diagram 2) 0 0))
    (E : perfectStableInfinity.{u} ⟶ _root_.SerrePositivity.KST.Spectra.Sp.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((ν ≫ E).app _ original)
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (((β_ _ _).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 2) ≫ ν ≫ E) 0 0) := by
  let c := (β_ (Δ[1] : SSet.{u + 1}) Δ[1]).hom ≫
    (stdSimplex.δ (2 : Fin 3) ▷ (Δ[1] : SSet.{u + 1}))
  exact d.sourceValueIso r E ≪≫
    (((e.comparison.precomp c).postcomp E).toNatIso.app
      (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (𝟙 (Δ[1] ⊗ Δ[1] : SSet.{u + 1})) 0 0)))

/-- 全図式比較後も、元の二本の屋根と同じ指定始域比較が可換。
四辺・上下二単体は e に指定され、ここではその同じ左上成分を合成する。 -/
lemma sourceValueIso_of_imageIso_triangle
    {F : (Δ[2] ⊗ Δ[1] : SSet.{u + 1}) ⟶ S}
    (b : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierRectangleBoundaryIso (d.diagram ≫ ν) (F ≫ ν))
    (e : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierRectangleDiagramIso (d.diagram ≫ ν) (F ≫ ν) b)
    {original : S _⦋0⦌}
    (r : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierSourceRoof ν original
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex ((β_ _ _).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare d.diagram 2) 0 0))
    (E : perfectStableInfinity.{u} ⟶ _root_.SerrePositivity.KST.Spectra.Sp.{u}) :
    (hoFunctor.map E).toFunctor.map ((hoFunctor.map ν).toFunctor.map
      (Truncated.HomotopyCategory.homMk r.augmentation)) ≫
        (d.sourceValueIso_of_imageIso b e r E).hom =
    (hoFunctor.map E).toFunctor.map ((hoFunctor.map ν).toFunctor.map
      (Truncated.HomotopyCategory.homMk r.comparison)) ≫
        (((e.comparison.precomp ((β_ (Δ[1] : SSet.{u + 1}) Δ[1]).hom ≫
          (stdSimplex.δ (2 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})))).postcomp E).toNatIso.app
            (HomotopyCategory.mk
              (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (𝟙 (Δ[1] ⊗ Δ[1] : SSet.{u + 1})) 0 0))).hom := by
  change _ ≫ ((r.valueIso E).hom ≫ _) = _
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun f => f ≫ _) (r.valueIso_triangle E))

end RelativePerfectVerdierRectangle
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierSourceRoof (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierSourceRoof := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierSourceRoof

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierRectangle.sourceRoofOfEq (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierRectangle.sourceRoofOfEq := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierRectangle.sourceRoofOfEq

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierRectangle.sourceValueIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierRectangle.sourceValueIso := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierRectangle.sourceValueIso

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierRectangle.sourceValueIso_of_imageIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierRectangle.sourceValueIso_of_imageIso := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierRectangle.sourceValueIso_of_imageIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierRectangle.sourceValueIso_of_imageIso_triangle := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierRectangle.sourceValueIso_of_imageIso_triangle

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierSourceRoof._sizeOf_1 (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierSourceRoof._sizeOf_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierSourceRoof._sizeOf_1

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierSourceRoof._sizeOf_inst (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierSourceRoof._sizeOf_inst := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierSourceRoof._sizeOf_inst

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierSourceRoof.augmentation (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierSourceRoof.augmentation := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierSourceRoof.augmentation

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierSourceRoof.augmentation_invertible := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierSourceRoof.augmentation_invertible

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierSourceRoof.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierSourceRoof.casesOn := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierSourceRoof.casesOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierSourceRoof.common (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierSourceRoof.common := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierSourceRoof.common

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierSourceRoof.comparison (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierSourceRoof.comparison := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierSourceRoof.comparison

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierSourceRoof.comparison_invertible := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierSourceRoof.comparison_invertible

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierSourceRoof.ctorIdx (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierSourceRoof.ctorIdx := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierSourceRoof.ctorIdx

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierSourceRoof.image (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierSourceRoof.image := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierSourceRoof.image

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierSourceRoof.mk (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierSourceRoof.mk := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierSourceRoof.mk

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierSourceRoof.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierSourceRoof.noConfusion := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierSourceRoof.noConfusion

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierSourceRoof.noConfusionType (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierSourceRoof.noConfusionType := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierSourceRoof.noConfusionType

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierSourceRoof.ofEq (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierSourceRoof.ofEq := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierSourceRoof.ofEq

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierSourceRoof.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierSourceRoof.rec := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierSourceRoof.rec

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierSourceRoof.recOn (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierSourceRoof.recOn := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierSourceRoof.recOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierSourceRoof.rectangleValueIso_of_imageIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierSourceRoof.rectangleValueIso_of_imageIso := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierSourceRoof.rectangleValueIso_of_imageIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierSourceRoof.rectangleValueIso_of_imageIso_triangle := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierSourceRoof.rectangleValueIso_of_imageIso_triangle

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierSourceRoof.triangle := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierSourceRoof.triangle

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierSourceRoof.valueIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierSourceRoof.valueIso := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierSourceRoof.valueIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierSourceRoof.valueIso_ofEq := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierSourceRoof.valueIso_ofEq

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierSourceRoof.valueIso_triangle := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierSourceRoof.valueIso_triangle

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierRectangle.sourceRoofOfEq._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierRectangle.sourceRoofOfEq._proof_1

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierSourceRoof.mk._flat_ctor (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierSourceRoof.mk._flat_ctor := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierSourceRoof.mk._flat_ctor

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierSourceRoof.mk.congr_simp := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierSourceRoof.mk.congr_simp

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierSourceRoof.mk.inj := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierSourceRoof.mk.inj

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierSourceRoof.mk.injEq := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierSourceRoof.mk.injEq

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierSourceRoof.mk.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierSourceRoof.mk.noConfusion := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierSourceRoof.mk.noConfusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierSourceRoof.mk.sizeOf_spec := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierSourceRoof.mk.sizeOf_spec

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierSourceRoof.ofEq._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierSourceRoof.ofEq._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierSourceRoof.ofEq._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierSourceRoof.ofEq._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierSourceRoof.ofEq.eq_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierSourceRoof.ofEq.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierSourceRoof.rectangleValueIso_of_imageIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierSourceRoof.rectangleValueIso_of_imageIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierSourceRoof.rectangleValueIso_of_imageIso._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierSourceRoof.rectangleValueIso_of_imageIso._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierSourceRoof.valueIso.eq_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierSourceRoof.valueIso.eq_1
