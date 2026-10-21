module

public import SerrePositivity.InfinityCategories.F2.CoherentTotalObject
public import SerrePositivity.InfinityCategories.F1B.KanHomotopyClasses
public import SerrePositivity.InfinityCategories.F1B.HomotopyWhiskering

/-!
概要：元の指定単位後の全空間射の同型を、元の Kan 置換射のホモトピーへ反映する。
方針：標的の頂点表示を戻し、単位の自然性と始域単位の弱同値で連結成分を反映する。
規約：元の二つの全空間射を保持し、底の quasicategory 性を要求しない。
使われ方：元の評価脚の Kan 像を、頂点比較と反復射影の Kan 合成へ照合する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の指定単位後の同型から、元の同じ二つの Kan 置換射のホモトピーを回収する。 -/
lemma coherentTotalKanMap_homotopy_of_unitIso {B C : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (G : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ SpaceInfinity.{u})
    {m n : smallLeftUnstraightening F ⟶ smallLeftUnstraightening G}
    (e : FunctorIso (m ≫ F2.coherentDiagramTotalUnit G) (n ≫ F2.coherentDiagramTotalUnit G)) :
    Nonempty (SSet.Homotopy (F2.continuousKanReplacement.map m)
      (F2.continuousKanReplacement.map n)) := by
  let H := functorHomotopyPostcomp e.simplicialHomotopy
    (eqToHom (F2.coherentDiagramTotalVertex_object G))
  have hm : (m ≫ F2.coherentDiagramTotalUnit G) ≫
      eqToHom (F2.coherentDiagramTotalVertex_object G) =
        m ≫ F2.continuousKanReplacementUnit.app (smallLeftUnstraightening G) := by
    rw [Category.assoc, F2.coherentDiagramTotalUnit_factor]
  have hn : (n ≫ F2.coherentDiagramTotalUnit G) ≫
      eqToHom (F2.coherentDiagramTotalVertex_object G) =
        n ≫ F2.continuousKanReplacementUnit.app (smallLeftUnstraightening G) := by
    rw [Category.assoc, F2.coherentDiagramTotalUnit_factor]
  let H' : SSet.Homotopy
      (m ≫ F2.continuousKanReplacementUnit.app (smallLeftUnstraightening G))
      (n ≫ F2.continuousKanReplacementUnit.app (smallLeftUnstraightening G)) :=
    { h := H.h, h₀ := H.h₀.trans hm, h₁ := H.h₁.trans hn, rel := H.rel }
  apply (functorVertex_piZero_eq_iff_homotopy _ _).mp
  apply (F2.continuousKanReplacementUnit_isWeakHomotopyEquivalence
    (smallLeftUnstraightening F) (F2.coherentDiagramTotalKan G)).injective
  change SSet.π₀.mk (functorVertex (F2.continuousKanReplacementUnit.app
    (smallLeftUnstraightening F) ≫ F2.continuousKanReplacement.map m)) =
    SSet.π₀.mk (functorVertex (F2.continuousKanReplacementUnit.app
      (smallLeftUnstraightening F) ≫ F2.continuousKanReplacement.map n))
  rw [← F2.continuousKanReplacementUnit.naturality m,
    ← F2.continuousKanReplacementUnit.naturality n]
  exact (functorVertex_piZero_eq_iff_homotopy _ _).mpr ⟨H'⟩

end SerrePositivity.InfinityCategories.HomotopyLimits
