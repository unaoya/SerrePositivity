module

public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationFiberComparison
public import SerrePositivity.InfinityCategories.F1.Categories.KanDiagramCoherentNerve
public import SerrePositivity.InfinityCategories.HomotopyLimits.WeightedConeSections

/-!
概要：strict な Kan 値図式の coherent な unstraightening と反転した豊穣係数の weighted nerve の比較。
方針：F2 の実際の coslice 比較と全 fiber の同値性を再利用し、left fibration の全空間判定を適用する。
規約：F2 のファイルは参照のみ。極限・余極限の存在は主張しない。
使われ方：Kerodon Corollary 5.6.0.6、strict な空間値図式と coherent な復元の接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 概要：Kan 値図式の coherent 表示は F2 の strict 図式の表示と一致する。
方針：各次数で同じ有限射列を同じ Kan 値図式へ後合成していることを確認する。
規約：対象と射の持ち上げ方の表示の違いを単体集合の射の等式で揃える。
使われ方：Kerodon Corollary 5.6.0.6、既存の実際の coslice 比較の再利用。 -/
lemma kanDiagramCoherentNerve_eq_strictCoherentDiagram
    {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) :
    kanDiagramCoherentNerve F = HomotopyLimits.strictCoherentDiagram F := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  rfl

/-- 概要：strict な空間値図式の一点からの coherent coslice 比較は全空間の前合成同値。
方針：反転した豊穣係数の weighted nerve と coslice の比較が全 fiber で同値なことを使う。
規約：係数は sHom(Δ⁰,F(c)) の反転であり、F(c) そのものとの厳密な同一視はしない。
使われ方：Kerodon Corollary 5.6.0.6、weighted nerve から coherent な unstraightening への比較。 -/
lemma weightedPointedKanComparison_isPrecompositionEquivalence
    {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) :
    IsPrecompositionEquivalence
      (HomotopyLimits.weightedCoherentConeComparison F pointKanObject) := by
  apply isPrecompositionEquivalence_of_leftFibration_fibers
    ((SSet.uliftFunctor.{u + 1, u}).map
      (weightedNerveProjection
        (HomotopyLimits.simplicialHomDiagram F pointKanObject ⋙ SSet.opFunctor)))
    (HomotopyLimits.coherentConeProjection (HomotopyLimits.strictCoherentDiagram F)
      (coherentNerveVertex pointKanObject))
    (HomotopyLimits.weightedCoherentConeComparison F pointKanObject)
    (HomotopyLimits.weightedCoherentConeComparison_over F pointKanObject)
  intro b
  exact (HomotopyLimits.weightedCoherentConeFiberMap_homotopyEquivalence
    F pointKanObject b).isQCatEquivalence

/-- 概要：図式と始点の等式による coslice の引き戻し全空間の移送は底への射影を保つ。
方針：二つの等式を消去し、恒等射の合成を計算する。
規約：全空間の等式の証明は任意でよい。
使われ方：Kerodon Remark 5.6.2.5、coherent な表示の変更による比較。 -/
lemma coherentConeTotal_transport_projection {K X : SSet.{u}} {F G : K ⟶ X}
    {x y : X _⦋0⦌} (hF : F = G) (hx : x = y)
    (h : HomotopyLimits.coherentConeTotal F x = HomotopyLimits.coherentConeTotal G y) :
    eqToHom h ≫ HomotopyLimits.coherentConeProjection G y =
      HomotopyLimits.coherentConeProjection F x := by
  subst G
  subst y
  simp

/-- 概要：strict 図式の一点からの coherent な錐の全空間は left unstraightening と同型。
方針：coherent 図式の表示と一点の頂点の等式で二つの pullback を同定する。
規約：通常の単体集合の同型であり、∞ 圏の極限は使わない。
使われ方：Kerodon Corollary 5.6.0.6、既存の coslice 比較の標的の同定。 -/
noncomputable def strictKanUnstraighteningIso
    {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) :
    HomotopyLimits.coherentConeTotal (HomotopyLimits.strictCoherentDiagram F)
      (coherentNerveVertex pointKanObject) ≅ leftUnstraightening (kanDiagramCoherentNerve F) :=
  eqToIso (by
    rw [kanDiagramCoherentNerve_eq_strictCoherentDiagram]
    change HomotopyLimits.coherentConeTotal _ (coherentNerveVertex pointKanObject) =
      HomotopyLimits.coherentConeTotal _ (spaceInfinityVertex pointKanObject)
    rw [spaceInfinityVertex_eq_coherent])

/-- 概要：strict な図式の coslice 全空間と unstraightening の同型は底への射影を保つ。
方針：図式と一点の頂点の等式による全空間の移送の計算を適用する。
規約：底は元の圏の nerve を u+1 に持ち上げたもの。
使われ方：Kerodon Remark 5.6.2.5、strict な復元比較が底上の射であることの確認。 -/
lemma strictKanUnstraighteningIso_projection
    {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) :
    (strictKanUnstraighteningIso F).hom ≫
      leftUnstraighteningProjection (kanDiagramCoherentNerve F) =
    HomotopyLimits.coherentConeProjection (HomotopyLimits.strictCoherentDiagram F)
      (coherentNerveVertex pointKanObject) := by
  let hd := (kanDiagramCoherentNerve_eq_strictCoherentDiagram F).symm
  let hx := (spaceInfinityVertex_eq_coherent pointKanObject).symm
  let h := congrArg₂ HomotopyLimits.coherentConeTotal hd hx
  change eqToHom h ≫ HomotopyLimits.coherentConeProjection
    (kanDiagramCoherentNerve F) (spaceInfinityVertex pointKanObject) = _
  exact coherentConeTotal_transport_projection hd hx h

/-- 概要：反転した一点からの豊穣係数の weighted nerve を、strict 図式の left unstraightening へ写す。
方針：既存の coslice 比較の標的を、coherent 表示と一点の頂点の等式で同定する。
規約：始域の係数の反転を明示し、底の宇宙は u+1 とする。
使われ方：Kerodon Corollary 5.6.0.6、coherent な空間値図式への実際の復元比較。 -/
noncomputable def strictKanUnstraighteningComparison
    {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) :
    (SSet.uliftFunctor.{u + 1, u}).obj
      (weightedNerve
        (HomotopyLimits.simplicialHomDiagram F pointKanObject ⋙ SSet.opFunctor)) ⟶
      leftUnstraightening (kanDiagramCoherentNerve F) :=
  HomotopyLimits.weightedCoherentConeComparison F pointKanObject ≫
    (strictKanUnstraighteningIso F).hom

/-- 概要：strict な図式の unstraightening への比較射は weighted nerve の射影を被覆する。
方針：標的の同型が底を保つ式に coslice 比較の底上の可換性を合成する。
規約：weighted nerve の係数は一点からの豊穣 Hom の反転。
使われ方：Kerodon Corollary 5.6.0.6、strict な復元の底上の比較図式。 -/
lemma strictKanUnstraighteningComparison_projection
    {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) :
    strictKanUnstraighteningComparison F ≫
      leftUnstraighteningProjection (kanDiagramCoherentNerve F) =
    (SSet.uliftFunctor.{u + 1, u}).map
      (weightedNerveProjection
        (HomotopyLimits.simplicialHomDiagram F pointKanObject ⋙ SSet.opFunctor)) := by
  rw [strictKanUnstraighteningComparison, Category.assoc, strictKanUnstraighteningIso_projection]
  exact HomotopyLimits.weightedCoherentConeComparison_over F pointKanObject

/-- 概要：strict な Kan 値図式の unstraightening への実際の比較射は前合成同値。
方針：標的の同定を戻し、coslice の全空間の比較の同値性を使う。
規約：特定の底上の射そのものの性質として記録する。
使われ方：Kerodon Corollary 5.6.0.6、strict 図式の coherent な復元比較の同値性。 -/
lemma strictKanUnstraighteningComparison_isPrecompositionEquivalence
    {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) :
    IsPrecompositionEquivalence (strictKanUnstraighteningComparison F) :=
  (weightedPointedKanComparison_isPrecompositionEquivalence F).comp
    (isPrecompositionEquivalence_of_iso (strictKanUnstraighteningIso F))

end SerrePositivity.InfinityCategories
