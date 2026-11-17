module

public import SerrePositivity.EInfinity.BarrattEccles.CarrierConstantDiagramPiZero
public import SerrePositivity.EInfinity.BarrattEccles.CarrierConstantDiagramFrameComparison
public import SerrePositivity.EInfinity.BarrattEccles.CarrierConstantDiagramSourceFunctor
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.PointwiseTensorSource

/-!
# 定値図式からの局所化 Hom 比較の始域自然性

概要：BM 命題 4.1・Hovey §5.4 の始域錐の π₀ 比較は元の始域複体の射に自然。
方針：図式 frame の Hom 同型の自然性と零次比較の逆の自然性を合成する。
規約：元の定値図式と実際の置換・零次同型を保持する。
使われ方：具体的な極限計算の導来 Hom 同値の始域自然性。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram

open CategoryTheory Limits _root_.HomotopicalAlgebra
open SerrePositivity.DifferentialGraded
open SerrePositivity.Reedy SerrePositivity.HomotopyFunctionComplex

attribute [local implicit_reducible] CofibrantResolutionFamily.atObject

variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

local instance : HasColimitsOfSize.{u, u} (Complex A) := ⟨fun _ _ => inferInstance⟩

local instance : HasColimitsOfSize.{0, u} (Complex A) :=
  hasColimitsOfSizeShrink.{0, u} _

/-- 概要：図式 frame の Hom 同型は始域複体の射に自然（Hovey §5.4）。
方針：同じ各値の実現随伴の係数自然性へ具体的な frame 射を代入する。
規約：始域錐の射は元の constantDiagramSourceMap。
使われ方：同じ零単体の代表で π₀ の前合成を計算する。 -/
lemma constantDiagramFrameHomIso_source {Y Z : (Complex A)} (f : Y ⟶ Z)
    (F : K ⥤ (Complex A)) :
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap ((constantDiagramFrameFamily A K).map f)).app F ≫
        ((constantDiagramFrameHomIso A K Y).app F).hom =
      ((constantDiagramFrameHomIso A K Z).app F).hom ≫ (constantDiagramSourceMap A K f).app F := by
  let := SerrePositivity.EInfinity.projectiveModelCategory A
  let q := cosimplicialResolutionFamily (carrierProbeFactorization A)
  exact _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseTensorFrameHomIso_source K (q.obj.map f)
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K) F

private lemma prefix_source {Y Z : (Complex A)} (f : Y ⟶ Z) :
    let := projectiveModelCategory A K
    let Q := (weakEquivalences (K ⥤ (Complex A))).Q
    ((constantDiagramLocalizedIso A K).app Y).inv ≫ Q.map (constantDiagramFrameZeroIso A K Y).inv ≫
        Q.map (((constantDiagramFrameFamily A K).map f).app (SimplexCategory.mk 0)) =
      Q.map ((Functor.const K).map f) ≫ ((constantDiagramLocalizedIso A K).app Z).inv ≫
        Q.map (constantDiagramFrameZeroIso A K Z).inv := by
  let := SerrePositivity.EInfinity.projectiveModelCategory A
  let := projectiveModelCategory A K
  let Q := (weakEquivalences (K ⥤ (Complex A))).Q
  have hz : (constantDiagramFrameZeroIso A K Y).inv ≫
        ((constantDiagramFrameFamily A K).map f).app (SimplexCategory.mk 0) =
      (constantDiagramReplacement A K).map f ≫ (constantDiagramFrameZeroIso A K Z).inv := by
    apply (cancel_mono (constantDiagramFrameZeroIso A K Z).hom).mp
    rw [Category.assoc, constantDiagramFrameZeroIso_naturality, Iso.inv_hom_id_assoc,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hn : Q.map ((Functor.const K).map f) ≫ ((constantDiagramLocalizedIso A K).app Z).inv =
      ((constantDiagramLocalizedIso A K).app Y).inv ≫
        Q.map ((constantDiagramReplacement A K).map f) :=
    (constantDiagramLocalizedIso A K).inv.naturality f
  change ((constantDiagramLocalizedIso A K).app Y).inv ≫ _ ≫ _ = _
  rw [← Q.map_comp, hz, Q.map_comp, ← Category.assoc, ← hn, Category.assoc]

/-- 概要：始域錐の π₀ と元の定値図式の Hom の比較は始域に自然（Hovey §5.4）。
方針：同じ frame Hom の零単体で計算し、零次比較と局所化比較の自然性を使う。
規約：前合成は元の複体射を定値図式に送って局所化したもの。
使われ方：一般極限の導来 Hom 比較の定値図式側の始域自然性。 -/
lemma constantDiagramSourcePiZeroEquiv_source {Y Z : (Complex A)} (f : Y ⟶ Z)
    (F : K ⥤ (Complex A)) (z : SSet.π₀ ((constantDiagramSourceHom A K Z).obj F)) :
    let := projectiveModelCategory A K
    let Q := (weakEquivalences (K ⥤ (Complex A))).Q
    constantDiagramSourcePiZeroEquiv A K Y F
        (SSet.mapπ₀ ((constantDiagramSourceMap A K f).app F) z) =
      Q.map ((Functor.const K).map f) ≫ constantDiagramSourcePiZeroEquiv A K Z F z := by
  let := SerrePositivity.EInfinity.projectiveModelCategory A
  let := projectiveModelCategory A K
  let Q := (weakEquivalences (K ⥤ (Complex A))).Q
  let e := (SSet.π₀Functor.mapIso ((constantDiagramFrameHomIso A K Z).app F)).toEquiv
  obtain ⟨z, rfl⟩ := e.surjective z
  induction z using SSet.π₀.rec with | mk h =>
  change constantDiagramSourcePiZeroEquiv A K Y F
      (SSet.mapπ₀ _ (SSet.mapπ₀ ((constantDiagramFrameHomIso A K Z).app F).hom (SSet.π₀.mk h))) =
    Q.map ((Functor.const K).map f) ≫ constantDiagramSourcePiZeroEquiv A K Z F
      (SSet.mapπ₀ ((constantDiagramFrameHomIso A K Z).app F).hom (SSet.π₀.mk h))
  have hn := (constantDiagramFrameHomIso_source A K f F).symm
  rw [← SSet.mapπ₀_comp_apply, hn, SSet.mapπ₀_comp_apply, SSet.mapπ₀_mk,
    constantDiagramSourcePiZeroEquiv_mk, constantDiagramSourcePiZeroEquiv_mk]
  change ((constantDiagramLocalizedIso A K).app Y).inv ≫
      Q.map (constantDiagramFrameZeroIso A K Y).inv ≫ Q.map
        (((constantDiagramFrameFamily A K).map f).app (SimplexCategory.mk 0) ≫ h) = _
  rw [Q.map_comp]
  simpa only [Category.assoc] using congrArg (fun g => g ≫ Q.map h) (prefix_source A K f)

end SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram
