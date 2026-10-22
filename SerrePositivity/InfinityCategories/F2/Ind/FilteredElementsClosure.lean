module

public import SerrePositivity.InfinityCategories.F2.Ind.OrdinaryFilteredElementsClosure
public import SerrePositivity.InfinityCategories.F2.Ind.FilteredPosetNerve
public import SerrePositivity.InfinityCategories.F2.Ind.CofinalCoconeRestriction
public import SerrePositivity.InfinityCategories.F2.Ind.CofinalUniverseLift
public import SerrePositivity.InfinityCategories.F2.Ind.RepresentableFilteredElements

/-!
概要：元の right unstraightening の元の圏の κ-filtered 条件は、前層内の全 κ-filtered 余極限で閉じる。
方針：同じ native 余錐を小さい cofinal poset に制限し、構成済みの coherent strict 化の保存を使う。
規約：正則 κ。添字・標的の宇宙を明示し、同じ元の頂点を保持する。
使われ方：HTT 5.3.5.4、最小閉包から right fibration 定義への逆方向。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) [Fact κ.IsRegular] (C : SSet.{u}) [Quasicategory C]

/-- 元の right unstraightening の元の圏の κ-filtered 条件は、全ての小さい κ-filtered 余極限で閉じる。 -/
lemma hasKappaFilteredElements_kappaColimitClosed :
    IsKappaColimitClosed κ (HasKappaFilteredElements κ (C := C)) := by
  intro K hK hFiltered F c hc hF
  obtain ⟨I, o, f, hI, hN, hf⟩ := exists_cofinal_kappaFiltered_poset (κ := κ) K
  letI := o
  have : IsCardinalFiltered I κ := hI
  let f' := (SSet.uliftFunctor.{u + 1, u}).map f
  have hc' : IsColimitCone (c.restrict f') :=
    (isColimitCone_iff_restrict_rightCofinal f' (isRightCofinal_ulift f hf) c).mp hc
  have hv := hasKappaFilteredElements_of_ordinary_colimit (f' ≫ F) (c.restrict f') hc'
    (fun i => hF (f.app (Opposite.op ⦋0⦌) i))
  simpa only [JoinCocone.vertex_restrict] using hv

/-- Indκ の最小閉包への所属は、同じ前層の元の right unstraightening の κ-filtered 性と同値。 -/
lemma isIndVertex_iff_hasKappaFilteredElements (v : (PresheafInfinity C) _⦋0⦌) :
    IsIndVertex κ C v ↔ HasKappaFilteredElements κ v := by
  constructor
  · exact isIndVertex_minimal κ (HasKappaFilteredElements κ (C := C))
      (hasKappaFilteredElements_yoneda κ)
      (hasKappaFilteredElements_isoClosed κ C)
      (hasKappaFilteredElements_kappaColimitClosed κ C)
  · exact isIndVertex_of_hasKappaFilteredElements κ

/-- 元の関手で書いた Indκ 条件は、元の right unstraightening の全空間に対する条件そのもの。 -/
lemma isIndVertex_functorVertex_iff
    (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u}) :
    IsIndVertex κ C (functorVertex F) ↔ IsKappaFiltered κ (smallRightUnstraightening F) :=
  (isIndVertex_iff_hasKappaFilteredElements κ C (functorVertex F)).trans
    (hasKappaFilteredElements_functorVertex κ F)

end SerrePositivity.InfinityCategories.F2.Ind
