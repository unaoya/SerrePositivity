module

public import SerrePositivity.InfinityCategories.HomotopyLimits.KanDiagramColimitTransport
public import SerrePositivity.InfinityCategories.F2.CoconeValEquality
public import SerrePositivity.InfinityCategories.Stable.SquareFunctorTransport
public import SerrePositivity.InfinityCategories.Stable.TrivialFibrationCocone

/-!
概要：同型な図式の指定余極限余錐の間で、元の関手による保存性を移す。
方針：可逆円柱へ元の余錐を延長し、同じ全余錐の両端で像の普遍性を比較する。
規約：頂点の同型だけを保存性の証拠にしない。使われ方：strict 化からの保存性の帰還。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Ind
open HomotopyLimits

/-- 図式の等号による全余錐の輸送は、像の余極限性を変えない。 -/
lemma mapJoinCocone_diagramEq_isColimit_iff {K X Y : SSet.{u}}
    (F : X ⟶ Y) {p q : K ⟶ X} (h : p = q) (c : JoinCocone p) :
    IsColimitCone (mapJoinCocone F (coherentCoconeOfDiagramEq h c)) ↔
      IsColimitCone (mapJoinCocone F c) := by
  cases h
  rfl

/-- 同値な単射の形状への制限は、元の関手による同じ余錐の像の普遍性を保ち反映する。 -/
lemma mapJoinCocone_isColimit_iff_restrict {A K X Y : SSet.{u}} [Quasicategory Y]
    (F : X ⟶ Y) (i : A ⟶ K) [Mono i] (hi : IsPrecompositionEquivalence i)
    {p : K ⟶ X} (c : JoinCocone p) :
    IsColimitCone (mapJoinCocone F c) ↔ IsColimitCone (mapJoinCocone F (c.restrict i)) := by
  have := sliceUnderRestrict_trivialKanFibration_of_precompositionEquivalence (p ≫ F) i hi
  have h := (qCatEquivalenceOfTrivialKanFibration
    (sliceUnderRestrict (p ≫ F) i)).isInitialVertex_iff (mapJoinCocone F c)
  exact h.trans (F2.isColimitCone_iff_of_cocone_val_eq _ _ (Category.assoc _ _ _).symm)

/-- 図式全体の関手同型で比較された指定 native 余極限の間で、像の余極限性を移す。 -/
lemma mapJoinCocone_isColimit_of_functorIso {K X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (F : X ⟶ Y) {p q : K ⟶ X}
    (e : FunctorIso p q) (c : JoinCocone p) (d : JoinCocone q)
    (hc : IsColimitCone c) (hd : IsColimitCone d)
    (hFc : IsColimitCone (mapJoinCocone F c)) : IsColimitCone (mapJoinCocone F d) := by
  obtain ⟨H, h₀, h₁⟩ := exists_equivalenceCylinder_extension_of_functorIso e
  let c₀ := coherentCoconeOfDiagramEq h₀.symm c
  have hc₀ : IsColimitCone c₀ := (coherentCoconeOfDiagramEq_isColimit_iff _ _).mp hc
  have hFc₀ : IsColimitCone (mapJoinCocone F c₀) :=
    (mapJoinCocone_diagramEq_isColimit_iff F _ _).mpr hFc
  obtain ⟨C, hC, hC₀, _⟩ := exists_colimitCocone_extension_of_precompositionEquivalence H
    (equivalenceCylinderEndpoint K false)
    (isPrecompositionEquivalence_equivalenceCylinderEndpoint K false) c₀ hc₀
  have hFC : IsColimitCone (mapJoinCocone F C) :=
    (mapJoinCocone_isColimit_iff_restrict F _
      (isPrecompositionEquivalence_equivalenceCylinderEndpoint K false) C).mpr
        (hC₀.symm ▸ hFc₀)
  let d₀ := coherentCoconeOfDiagramEq h₁ (C.restrict (equivalenceCylinderEndpoint K true))
  have := sliceUnderRestrict_trivialKanFibration_of_precompositionEquivalence H
    (equivalenceCylinderEndpoint K true)
    (isPrecompositionEquivalence_equivalenceCylinderEndpoint K true)
  have hd₀ : IsColimitCone d₀ :=
    (coherentCoconeOfDiagramEq_isColimit_iff _ _).mp
      (((qCatEquivalenceOfTrivialKanFibration (sliceUnderRestrict H
        (equivalenceCylinderEndpoint K true))).isInitialVertex_iff C).mp hC)
  have hFd₀ : IsColimitCone (mapJoinCocone F d₀) :=
    (mapJoinCocone_diagramEq_isColimit_iff F _ _).mpr
      ((mapJoinCocone_isColimit_iff_restrict F _
        (isPrecompositionEquivalence_equivalenceCylinderEndpoint K true) C).mp hFC)
  exact hFd₀.of_functorIso
    ((coconeFunctorIsoOfVertexIso d₀ d (colimitConeIso d₀ d hd₀ hd)).postcomp F)

end SerrePositivity.InfinityCategories.F2.Ind
