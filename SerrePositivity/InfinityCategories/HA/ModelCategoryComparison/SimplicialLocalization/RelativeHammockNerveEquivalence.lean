module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RelativeHammockEnriched
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.HammockInvertsEdges
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.WeakNerveInverts
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulEquivalence

/-!
概要：同じ相対変形による hammock 比較を全 coherent nerve の同値へ上げる。
方針：全 Hom の弱比較から充満忠実性、元の弱単位から本質的全射性を得る。
規約：元の全関手と指定単位を保持する。
使われ方：bifibrant 部分圏から同じ cofibrant 局所化への復帰。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open _root_.CategoryTheory _root_.SSet
open _root_.SerrePositivity.InfinityCategories
variable {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}}
  (F : LocalizerMorphism C.weakEquivalences D.weakEquivalences)
  (G : LocalizerMorphism D.weakEquivalences C.weakEquivalences)
  (η : 𝟭 D.category ⟶ G.functor ⋙ F.functor)
  (hη : ∀ Y, D.weakEquivalences (η.app Y))

include G η hη in
/-- 概要：元の弱単位は同じ hammock coherent nerve 比較の本質的全射性を与える。
方針：同じ逆候補の対象像を取り、単位の局所化像を反転する。
規約：元の弱単位と同じ代表頂点。使われ方：全比較の QCat 同値判定。 -/
lemma relativeKanHammockNerve_essentiallySurjective :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsEssentiallySurjective (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.relativeKanHammockNerve F) := by
  intro y
  let Y : D.category := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject (C := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanHammockCategory D) y
  let X : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanHammockCategory C := G.functor.obj Y
  have hi := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.weakNerveEdges_inverts_arrows D _ (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap_inverts D)
    (η.app Y) (hη Y)
  let e := asIso (Truncated.HomotopyCategory.homMk
    ((nerve.edgeMk (η.app Y)).map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap D)).toTruncated)
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X, ⟨?_⟩⟩
  refine eqToIso (congrArg HomotopyCategory.mk ?_) ≪≫ e.symm ≪≫
    eqToIso (congrArg HomotopyCategory.mk ?_)
  · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_vertex (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.relativeKanHammockFunctor F) X).trans
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap_vertex D (F.functor.obj X)).symm
  · exact (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap_vertex D Y).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object (C := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanHammockCategory D) y)

include G η hη in
/-- 概要：同じ全 Hom の弱比較と元の弱単位から全 coherent nerve の同値を得る。
方針：元の充満忠実性と本質的全射性を一般判定へ渡す。
規約：点ごとの Hom 同値へ結論を弱めない。使われ方：局所化普遍性の全族輸送。 -/
lemma relativeKanHammockNerve_isQCatEquivalence
    (hF : ∀ X Y, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Relative.colimitMap F X Y)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.relativeKanHammockNerve F) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective _
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.relativeKanHammockNerve_fullyFaithful F hF)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.relativeKanHammockNerve_essentiallySurjective F G η hη)

omit η hη in
/-- 概要：元の弱余単位も同じ全 nerve 比較の本質的全射性を与える。
方針：余単位の同じ局所化像をその向きのまま使う。
規約：元の余単位を保持。使われ方：全圏への cofibrant 包含の比較。 -/
lemma relativeKanHammockNerve_essentiallySurjective_of_counit
    (ε : G.functor ⋙ F.functor ⟶ 𝟭 D.category)
    (hε : ∀ Y, D.weakEquivalences (ε.app Y)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsEssentiallySurjective (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.relativeKanHammockNerve F) := by
  intro y
  let Y : D.category := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject (C := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanHammockCategory D) y
  let X : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanHammockCategory C := G.functor.obj Y
  have hi := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.weakNerveEdges_inverts_arrows D _ (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap_inverts D)
    (ε.app Y) (hε Y)
  let e := asIso (Truncated.HomotopyCategory.homMk
    ((nerve.edgeMk (ε.app Y)).map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap D)).toTruncated)
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X, ⟨?_⟩⟩
  refine eqToIso (congrArg HomotopyCategory.mk ?_) ≪≫ e ≪≫
    eqToIso (congrArg HomotopyCategory.mk ?_)
  · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_vertex (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.relativeKanHammockFunctor F) X).trans
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap_vertex D (F.functor.obj X)).symm
  · exact (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap_vertex D Y).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object (C := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanHammockCategory D) y)

omit η hη in
/-- 概要：同じ全 Hom 比較と元の弱余単位から全 coherent nerve の同値を得る。
方針：全 Hom の充満忠実性と同じ余単位による本質的全射性を合成する。
規約：元の相対関手自身。使われ方：全モデル圏への実 cofibrant 包含の比較。 -/
lemma relativeKanHammockNerve_isQCatEquivalence_of_counit
    (ε : G.functor ⋙ F.functor ⟶ 𝟭 D.category)
    (hε : ∀ Y, D.weakEquivalences (ε.app Y))
    (hF : ∀ X Y, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Relative.colimitMap F X Y)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.relativeKanHammockNerve F) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective _
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.relativeKanHammockNerve_fullyFaithful F hF)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.relativeKanHammockNerve_essentiallySurjective_of_counit F G ε hε)

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
