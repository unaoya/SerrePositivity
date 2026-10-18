module

public import SerrePositivity.InfinityCategories.F1.DirectKanCoefficients
public import SerrePositivity.InfinityCategories.F1.WeightedKanEdgewiseComparison
public import SerrePositivity.InfinityCategories.F1.LeftFibrationSpanStrictification
public import SerrePositivity.InfinityCategories.F1.UniverseQCatEquivalence

/-!
概要：Kan 値通常図式の weighted nerve を、その図式自身の coherent な復元へ比較する。
方針：edgewise 解像の右比較を底上で逆向きに取り、左比較と豊穣係数の比較を合成する。
規約：図式の値は反転しない。比較射の選択は非計算的。
使われ方：Kerodon Corollary 5.6.0.6、直値の strict transport による復元。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：Kan 値図式の weighted nerve から直値の coherent な復元への底上の同値射が存在する。
方針：共通解像への底上の逆比較を選び、反転係数を経由する比較へ合成する。
規約：底と元の全空間を u+1 に持ち上げる。
使われ方：Kerodon Corollary 5.6.0.6、strict 図式とその coherent 表示の全空間比較。 -/
lemma exists_directKanUnstraighteningComparison
    {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) :
    ∃ f : (SSet.uliftFunctor.{u + 1, u}).obj (weightedNerve (F ⋙ kanObjectForget)) ⟶
        leftUnstraightening (kanDiagramCoherentNerve F),
      f ≫ leftUnstraighteningProjection (kanDiagramCoherentNerve F) =
        (SSet.uliftFunctor.{u + 1, u}).map (weightedNerveProjection (F ⋙ kanObjectForget)) ∧
      IsPrecompositionEquivalence f := by
  have : ∀ c, ((F ⋙ kanObjectForget).obj c).KanComplex :=
    fun c => inferInstanceAs (F.obj c).obj.KanComplex
  have : ∀ c, ((F ⋙ kanEdgewiseFunctor ⋙ kanObjectForget).obj c).KanComplex :=
    fun c => inferInstanceAs (kanEdgewiseFunctor.obj (F.obj c)).obj.KanComplex
  have : ∀ c, ((F ⋙ kanObjectOpFunctor ⋙ kanObjectForget).obj c).KanComplex :=
    fun c => inferInstanceAs (kanObjectOpFunctor.obj (F.obj c)).obj.KanComplex
  let p := weightedNerveProjection (F ⋙ kanObjectForget)
  let q := weightedNerveProjection (F ⋙ kanEdgewiseFunctor ⋙ kanObjectForget)
  obtain ⟨g, hg, eg⟩ := exists_leftFibration_comparison_of_span p q q
    (weightedKanEdgewiseRight F) (𝟙 _) (weightedKanEdgewiseRight_projection F)
    (Category.id_comp q) (weightedKanEdgewiseRight_isPrecompositionEquivalence F)
    (isPrecompositionEquivalence_id _)
  let U := SSet.uliftFunctor.{u + 1, u}
  refine ⟨U.map (g ≫ weightedKanEdgewiseLeft F) ≫
    reversedWeightedKanUnstraighteningComparison F, ?_, ?_⟩
  · rw [Category.assoc, reversedWeightedKanUnstraighteningComparison_projection,
      ← U.map_comp, Category.assoc, weightedKanEdgewiseLeft_projection, hg]
  · have he := (eg.comp (weightedKanEdgewiseLeft_isPrecompositionEquivalence F)).isQCatEquivalence.ulift.{u, u + 1}
    exact he.isPrecompositionEquivalence.comp
      (reversedWeightedKanUnstraighteningComparison_isPrecompositionEquivalence F)

/-- 概要：Kan 値通常図式と直値の coherent な復元を結ぶ実際の比較射。
方針：底を保つ前合成同値射の存在から選ぶ。
規約：自然性を選択した射に要求せず、存在と底上の可換性を用いる。
使われ方：Kerodon Corollary 5.6.0.6、直値の図式の復元 API。 -/
noncomputable def directKanUnstraighteningComparison
    {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) :
    (SSet.uliftFunctor.{u + 1, u}).obj (weightedNerve (F ⋙ kanObjectForget)) ⟶
      leftUnstraightening (kanDiagramCoherentNerve F) :=
  (exists_directKanUnstraighteningComparison F).choose

/-- 概要：直値の coherent な復元への比較射は底を厳密に保つ。
方針：選択した射の存在条件を取り出す。
規約：底は nerve C の u+1 への持ち上げ。
使われ方：Kerodon Remark 5.6.2.5、元の射影との合成。 -/
lemma directKanUnstraighteningComparison_projection
    {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) :
    directKanUnstraighteningComparison F ≫
      leftUnstraighteningProjection (kanDiagramCoherentNerve F) =
      (SSet.uliftFunctor.{u + 1, u}).map (weightedNerveProjection (F ⋙ kanObjectForget)) :=
  (exists_directKanUnstraighteningComparison F).choose_spec.1

/-- 概要：直値の coherent な復元への比較射は全空間の前合成同値。
方針：選択した射の同値性を取り出す。
規約：実際の底上の比較射そのものの性質。
使われ方：Kerodon Corollary 5.6.0.6、strict transport の復元比較の合成。 -/
lemma directKanUnstraighteningComparison_isPrecompositionEquivalence
    {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) :
    IsPrecompositionEquivalence (directKanUnstraighteningComparison F) :=
  (exists_directKanUnstraighteningComparison F).choose_spec.2

end SerrePositivity.InfinityCategories
