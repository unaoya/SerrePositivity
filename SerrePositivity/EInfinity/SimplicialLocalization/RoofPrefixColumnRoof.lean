module
public import SerrePositivity.EInfinity.SimplicialLocalization.RoofPrefixFamilyTriangle
public import SerrePositivity.EInfinity.SimplicialLocalization.WeakNerveInverts
public import SerrePositivity.EInfinity.FrameHom.NerveColumnRoofNaturality
public import SerrePositivity.EInfinity.ComplexLimits.PinchedFamilyPostcompArrow
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.FunctorHomotopyClasses
/-! 概要：実 hammock roof 全族の任意の後合成を元の通常列の全屋根へ戻す。
方針：全評価三角形の両円柱を同じ後合成で送り、元の左脚の逆を保持する。
規約：同じ全添字・端点表示・augmentation・評価を保持する。
使われ方：実 U の全源比較と同じ複体屋根への接合。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplicialLocalization.RoofPrefix
open CategoryTheory SSet MonoidalClosed
open SerrePositivity.InfinityCategories SerrePositivity.EInfinity.FrameHom
open scoped Simplicial
variable (C : RelativeCategory.{u}) {I : Type u} [Category.{u} I]
  (V : I ⥤ C.category) {X Y : C.category} (p : V ⟶ (Functor.const I).obj X)
  (hp : ∀ i, C.weakEquivalences (p.app i)) (s : V ⟶ (Functor.const I).obj Y)
  (hV : ∀ {i j} (a : i ⟶ j), C.weakEquivalences (V.map a))

/-- 概要：同じ全 Arrow の逆も一致する。
方針：両端の等式を消去する。規約：元の射を保持。
使われ方：同じ実屋根の左脚の反転。 -/
lemma inv_arrow_eq {D : Type*} [Category* D] {a b a' b' : D}
    (f : a ⟶ b) (g : a' ⟶ b') [IsIso f] [IsIso g]
    (h : Arrow.mk f = Arrow.mk g) : Arrow.mk (inv f) = Arrow.mk (inv g) := by
  obtain ⟨ha, hb, hh⟩ := (Arrow.mk_eq_mk_iff f g).mp h
  cases ha
  cases hb
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hh
  cases hh
  rfl

/-- 概要：同じ二つの全 Arrow の合成も一致する。
方針：三端点の等式を消去する。規約：元の合成を保持。
使われ方：元の全屋根の比較。 -/
lemma comp_arrow_eq {D : Type*} [Category* D] {a b c a' b' c' : D}
    (f : a ⟶ b) (g : b ⟶ c) (f' : a' ⟶ b') (g' : b' ⟶ c')
    (hf : Arrow.mk f = Arrow.mk f') (hg : Arrow.mk g = Arrow.mk g') :
    Arrow.mk (f ≫ g) = Arrow.mk (f' ≫ g') := by
  obtain ⟨ha, hb, hf⟩ := (Arrow.mk_eq_mk_iff f f').mp hf
  obtain ⟨_, hc, hg⟩ := (Arrow.mk_eq_mk_iff g g').mp hg
  cases ha
  cases hb
  cases hc
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hf hg
  cases hf
  cases hg
  rfl

include hp in
/-- 概要：全弱左脚は実 hammock からの任意の後合成で反転される。
方針：元の全指定辺の反転と後合成を使う。
規約：元の同じ弱射を保持。使われ方：全屋根像の左脚の逆。 -/
lemma postcomp_augmentation_invertible {E : SSet.{u}}
    (F : kanHammockNerve C ⟶ E) (i : I) :
    IsInvertibleEdge ((nerve.edgeMk (p.app i)).map
      (hammockLocalizationNerveMap C ≫ F)).toTruncated :=
  weakNerveEdges_inverts_arrows C _ ((hammockLocalizationNerveMap_inverts C).comp F) _ (hp i)

/-- 概要：全左脚・評価の円柱像は同じ通常自然変換の全像。
方針：元の全円柱の厳密な後合成式を使う。
規約：端点表示を Arrow 等式で保持。使われ方：実屋根像の比較。 -/
lemma coherentAugmentation_postcomp_arrow {E : SSet.{u}}
    (F : kanHammockNerve C ⟶ E) {Z : C.category}
    (a : V ⟶ (Functor.const I).obj Z) :
    let T := (hoFunctor.map ((ihom (nerve I)).map F)).toFunctor
    Arrow.mk (T.map (Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy (coherentAugmentationHomotopy C V a)))) =
    Arrow.mk (NerveColumn.hom (hammockLocalizationNerveMap C ≫ F) a) := by
  dsimp only
  rw [← functorHomotopyPostcomp_hom]
  have h := functorHomotopy_hom_arrow_of_h_eq
    (functorHomotopyPostcomp (coherentAugmentationHomotopy C V a) F)
    (functorHomotopyPostcomp (F1B.nerveNatTransHomotopy a)
      (hammockLocalizationNerveMap C ≫ F)) (Category.assoc _ _ _)
  refine h.trans ?_
  apply congrArg Arrow.mk
  rw [functorHomotopyPostcomp_hom]
  have hb : Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy (F1B.nerveNatTransHomotopy a)) =
      F1B.nerveNatTransHom a := F1B.nerveNatTransHomotopy_hom a
  rw [hb]
  rfl

/-- 概要：元の全 native roof の像は同じ通常列の全屋根。
方針：全 Arrow 比較と同じ二つの円柱の像を接続する。
規約：実全族自身と同じ左脚の逆を保持。使われ方：U の全源比較。 -/
lemma native_family_postcomp_column_roof_arrow {E : SSet.{u}} [Quasicategory E]
    (F : kanHammockNerve C ⟶ E) :
    Arrow.mk (intervalFamilyHom ((familyMap C V p hp s hV ≫
      kanHammockHomPinchedMap C X Y) ≫ pinchedHomMap F _ _ ≫
        pinchedHomToIntervalMappingSpace _ _)) =
    Arrow.mk ((NerveColumn.augmentationIso (hammockLocalizationNerveMap C ≫ F) V p
      (postcomp_augmentation_invertible C V p hp F)).inv ≫
      NerveColumn.hom (hammockLocalizationNerveMap C ≫ F) s) := by
  let T := (hoFunctor.map ((ihom (nerve I)).map F)).toFunctor
  have hn := native_family_eq_roof_arrow C V p hp s hV
  have hm := congrArg T.mapArrow.obj hn
  have hl := ComplexLimits.pinchedFamilyPostcomp_arrow F
    (familyMap C V p hp s hV ≫ kanHammockHomPinchedMap C X Y)
  refine hl.trans (hm.trans ?_)
  change Arrow.mk (T.map ((coherentAugmentationIso C V p hp).inv ≫ _)) = _
  rw [Functor.map_comp]
  apply comp_arrow_eq
  · have hi : Arrow.mk (T.map (coherentAugmentationIso C V p hp).hom) =
        Arrow.mk (NerveColumn.hom (hammockLocalizationNerveMap C ≫ F) p) :=
      coherentAugmentation_postcomp_arrow C V F p
    rw [← NerveColumn.augmentationIso_hom _ V p
      (postcomp_augmentation_invertible C V p hp F)] at hi
    simpa only [← Functor.map_inv, IsIso.Iso.inv_hom] using inv_arrow_eq _ _ hi
  · exact coherentAugmentation_postcomp_arrow C V F s

end SerrePositivity.EInfinity.SimplicialLocalization.RoofPrefix
