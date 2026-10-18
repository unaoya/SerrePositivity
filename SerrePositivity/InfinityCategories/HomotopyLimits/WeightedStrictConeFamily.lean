module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SmallStrictConeParameter
public import SerrePositivity.InfinityCategories.HomotopyLimits.StrictConeNativeComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.ReflectedStrictConeEvaluation

/-!
概要：始対象を加えた strict な図式の weighted な比較を、錐の図式全体へ引き戻す。
方針：始対象からの標準錐を Hom の weighted 比較へ渡し、錐の形の標準射で前合成する。
規約：頂点評価の切断の選択は用いず、構成済みの q′ の比較から実際の族を作る。
使われ方：HTT 4.2.4.1、Kerodon 7.5.4.6 の q′ と native な制限の接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C]

/-- 概要：小さい始対象付き錐の図式に、始対象の像を頂点とする標準錐を与える。
方針：各脚を始対象からの射の関手像とする。
規約：錐の頂点は元の c.pt に定義的に一致する。
使われ方：Kerodon 7.5.4.6 の全図式上の反転 Hom の比較への入力。 -/
def smallStrictConeExtension {F : I ⥤ C} (c : Cone F) : Cone (smallStrictConeFunctor c) where
  pt := c.pt
  π :=
    { app := fun j ↦ (smallStrictConeFunctor c).map (WithInitial.starInitial.to j)
      naturality := by
        intro j k f
        change 𝟙 ((smallStrictConeFunctor c).obj WithInitial.star) ≫
          (smallStrictConeFunctor c).map (WithInitial.starInitial.to k) = _
        rw [Category.id_comp, ← CategoryTheory.Functor.map_comp]
        congr 1 }

/-- 概要：始対象付き図式の標準錐の元の対象への脚は元の錐の脚。
方針：始対象から元の対象への射の像を計算する。
規約：通常の圏の射の厳密な等式。
使われ方：Kerodon 7.5.4.6 の元の q′ の比較との照合。 -/
lemma smallStrictConeExtension_app_of {F : I ⥤ C} (c : Cone F) (i : I) :
    (smallStrictConeExtension c).π.app (WithInitial.of i) = c.π.app i := rfl

/-- 概要：始対象付き図式の標準錐の始対象への脚は恒等射。
方針：始対象の自己射への関手の作用を計算する。
規約：頂点は c.pt。
使われ方：Kerodon 7.5.4.6 の weighted な切断比較の頂点評価。 -/
lemma smallStrictConeExtension_app_star {F : I ⥤ C} (c : Cone F) :
    (smallStrictConeExtension c).π.app WithInitial.star = 𝟙 c.pt := rfl

/-- 概要：始対象付き図式の標準錐を元の図式へ制限すると元の錐になる。
方針：錐の頂点と各脚を定義で計算する。
規約：自然同型ではなく錐の等号。
使われ方：HTT 4.2.4.1 の元の strict な錐の比較との整合性。 -/
lemma smallStrictConeExtension_whisker {F : I ⥤ C} (c : Cone F) :
    (smallStrictConeExtension c).whisker WithInitial.incl = c := rfl

/-- 概要：小さい始対象付き図式への標準射は錐の左頂点を新しい始対象へ写す。
方針：左包含上の射の等式を零単体で評価する。
規約：ULift した nerve の頂点の厳密な等号。
使われ方：Kerodon 7.5.4.6 の引き戻した weighted な族の頂点での値。 -/
lemma smallStrictConeParameter_apex (I : Type u) [SmallCategory I] :
    (smallStrictConeParameter.{u, v} I).app (Opposite.op ⦋0⦌)
        (joinApexVertex ((SSet.uliftFunctor.{v, u}).obj (nerve I))) =
      ULift.up (nerveVertex (WithInitial.star : WithInitial I)) := by
  change (joinInl (Δ[0] : SSet.{max u v}) _ ≫ smallStrictConeParameter I).app
    (Opposite.op ⦋0⦌) (SSet.stdSimplex.obj₀Equiv.symm 0) = _
  rw [smallStrictConeParameter_inl, SSet.yonedaEquiv_symm_zero]
  simp [SSet.const]

/-- 概要：図式の等式で相対関手空間を移送しても展開した族は変わらない。
方針：図式の等式で置換して恒等射への後合成を除く。
規約：射影 q と図式の始域は共通。
使われ方：Kerodon 7.4.1.6 の正規化した切断の引き戻しの値。 -/
lemma relativeFunctorUncurry_eqToHom {A K E B : SSet.{u}} (q : E ⟶ B)
    {p r : K ⟶ B} (h : p = r) (s : A ⟶ relativeFunctorSpace q p) :
    relativeFunctorUncurry (s ≫
      eqToHom (congrArg (fun f : K ⟶ B ↦ relativeFunctorSpace q f) h)) =
      relativeFunctorUncurry s := by
  cases h
  rw [eqToHom_refl, Category.comp_id]

variable [SimplicialCategory C]

/-- 概要：weighted な反転 Hom の比較から strict な錐の図式全体上の切断の族を作る。
方針：始対象付き図式の標準錐の q′ の比較を錐の形の標準射で引き戻す。
規約：頂点評価の逆の選択を使わない実際の比較射。
使われ方：HTT 4.2.4.1 の q′ と native な切断の制限を接続する族。 -/
noncomputable def weightedStrictConeFamilyComparison {F : I ⥤ C} (c : Cone F) (x : C) :
    (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom x c.pt).op ⟶
      coherentConeSectionSpace (strictCoherentCone c).val (coherentNerveVertex x) :=
  reflectedStrictConeSectionsComparison (smallStrictConeExtension c) x ≫
    relativeFunctorPre
      (sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex x)))
      (strictCoherentDiagram (smallStrictConeFunctor c)) (smallStrictConeParameter I) ≫
    eqToHom (congrArg (fun p ↦ coherentConeSectionSpace p (coherentNerveVertex x))
      (smallStrictConeParameter_diagram c))

/-- 概要：weighted な族を展開すると元の比較の族を標準射で前合成したものになる。
方針：図式の等式による移送を除き、相対前合成の自然性を使う。
規約：全 Hom パラメータでの厳密な式。
使われ方：Kerodon 7.5.4.6 の元の図式への制限と頂点での評価の同時追跡。 -/
lemma weightedStrictConeFamilyComparison_uncurry {F : I ⥤ C} (c : Cone F) (x : C) :
    relativeFunctorUncurry (weightedStrictConeFamilyComparison c x) =
      (smallStrictConeParameter I ▷
        (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom x c.pt).op) ≫
          relativeFunctorUncurry
            (reflectedStrictConeSectionsComparison (smallStrictConeExtension c) x) := by
  rw [weightedStrictConeFamilyComparison, ← Category.assoc,
    relativeFunctorUncurry_eqToHom _ (smallStrictConeParameter_diagram c),
    relativeFunctorUncurry_pre]

/-- 概要：strict な錐の頂点評価の包含後の値は通常の内部 Hom の評価。
方針：strict な頂点の等号の移送を除き、一般の錐の評価の包含の式を使う。
規約：終域の fiber は元の c.pt に正規化してある。
使われ方：Kerodon 7.5.4.6 の weighted な族の頂点での値の同定。 -/
lemma strictConeApexEvaluation_ι {F : I ⥤ C} (c : Cone F) (x : C) :
    strictConeApexEvaluation c x ≫
        vertexFiberι (sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex x)))
          (coherentNerveVertex c.pt) =
      vertexFiberι ((ihom (join (Δ[0] : SSet.{max u v})
        ((SSet.uliftFunctor.{v, u}).obj (nerve I)))).map
          (sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex x))))
        (functorVertex (strictCoherentCone c).val) ≫
          evaluateFunctorAt (joinApexVertex ((SSet.uliftFunctor.{v, u}).obj (nerve I))) := by
  have ht {E B : SSet.{max u v}} (q : E ⟶ B) {y z : B _⦋0⦌} (h : y = z) :
      eqToHom (congrArg (fun b : B _⦋0⦌ ↦ vertexFiber q b) h) ≫ vertexFiberι q z =
        vertexFiberι q y := by cases h; exact Category.id_comp _
  rw [strictConeApexEvaluation, Category.assoc, ht _ (strictCoherentCone_vertex c),
    coneApexSectionEvaluation_ι]

/-- 概要：相対関手のパラメータの族を一点で評価する式。
方針：内部 Hom の評価と curry の往復を使う。
規約：q、p、族 s に充填性は不要。
使われ方：Kerodon 7.4.1.6 の全パラメータでの頂点評価。 -/
lemma relativeFunctorUncurry_at_vertex {A K E B : SSet.{u}} (q : E ⟶ B)
    (p : K ⟶ B) (s : A ⟶ relativeFunctorSpace q p) (v : K _⦋0⦌) :
    s ≫ vertexFiberι ((ihom K).map q) (functorVertex p) ≫ evaluateFunctorAt v =
      lift (SSet.const v) (𝟙 A) ≫ relativeFunctorUncurry s := by
  rw [relativeFunctorUncurry, ← curry_evaluateFunctorAt_vertex, curry_uncurry, Category.assoc]

set_option maxHeartbeats 1200000 in
-- 始対象での図式と錐の頂点の定義的な同一視を含む評価式の型検査に使う。
/-- 概要：weighted な錐の族を頂点で評価すると標準の coslice fiber 比較に一致する。
方針：引き戻しの展開と始対象への脚が恒等であることを使い、既存の全 Hom 評価を適用する。
規約：頂点評価の切断の選択を使わず、Kan 性や極限性も不要。
使われ方：HTT 4.2.4.1 の q′ から構成する族の始域の同値性の検査。 -/
lemma weightedStrictConeFamilyComparison_evaluation {F : I ⥤ C} (c : Cone F) (x : C) :
    weightedStrictConeFamilyComparison c x ≫ strictConeApexEvaluation c x =
      coherentCosliceFiberComparison x c.pt := by
  apply vertexFiber_hom_ext
    (sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex x)))
    (coherentNerveVertex c.pt)
  rw [Category.assoc, strictConeApexEvaluation_ι,
    relativeFunctorUncurry_at_vertex, weightedStrictConeFamilyComparison_uncurry,
    ← Category.assoc, lift_whiskerRight, SSet.const_comp,
    smallStrictConeParameter_apex]
  have he := reflectedStrictConeSectionsComparison_evaluate
    (smallStrictConeExtension c) x WithInitial.star
  simp only [smallStrictConeExtension_app_star] at he
  change _ = (SSet.uliftFunctor.{v, u}).map (SSet.opFunctor.map
    (((SimplicialCategory.sHomFunctor C).obj (Opposite.op x)).map (𝟙 c.pt))) ≫
      coherentCosliceFiberComparison x c.pt ≫
      vertexFiberι (sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex x)))
        (coherentNerveVertex c.pt) at he
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_id, Category.id_comp] at he
  exact he

variable [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]

/-- 概要：weighted な反転 Hom の比較を引き戻した錐の族は単体的ホモトピー同値。
方針：頂点での coslice 比較と trivial Kan な評価に二対三則を使う。
規約：始対象付き図式全体の Bousfield–Kan 比較の同値性を仮定しない。
使われ方：HTT 4.2.4.1 の元の q′ と native な制限の比較の始域。 -/
lemma weightedStrictConeFamilyComparison_homotopyEquivalence {F : I ⥤ C}
    (c : Cone F) (x : C) :
    IsSimplicialHomotopyEquivalence (weightedStrictConeFamilyComparison c x) := by
  have := vertexFiber_kanComplex_of_leftFibration
    (sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex x)))
    (coherentNerveVertex c.pt)
  have := strictConeApexEvaluation_trivialKanFibration c x
  have he : IsQCatEquivalence (strictConeApexEvaluation c x) :=
    (qCatEquivalenceOfTrivialKanFibration (strictConeApexEvaluation c x)).isQCatEquivalence
  apply (he.cancel_right ?_).isSimplicialHomotopyEquivalence
  rw [weightedStrictConeFamilyComparison_evaluation]
  exact (coherentCosliceFiberComparison_homotopyEquivalence x c.pt).isQCatEquivalence

end SerrePositivity.InfinityCategories.HomotopyLimits
