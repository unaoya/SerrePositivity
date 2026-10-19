module

public import SerrePositivity.InfinityCategories.HomotopyLimits.KanSourceReplacement
public import SerrePositivity.InfinityCategories.HomotopyLimits.StrictConeReindex
public import SerrePositivity.InfinityCategories.HomotopyLimits.GeneralReflectedCriterion

/-!
概要：台の通常の余錐の頂点を Kan 置換し、全反変 Hom と native な余極限性を比較する。
方針：置換の単位による内部 Hom の前合成を錐の射とし、反転 end の比較を厳密に分解する。
規約：元の余錐の頂点の Kan 性や余極限性は構成に要求しない。
使われ方：HTT 4.2.4.1、通常の押し出しから実際の homotopy 押し出しへの移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {I J : Type u} [SmallCategory I] [SmallCategory J]
  {F : I ⥤ KanObject.{u}}

local instance anodyneCoconeOppositeHomKan (X Y : KanObject.{u}ᵒᵖ) :
    KanComplex (SimplicialCategory.sHom X Y) :=
  inferInstanceAs (KanComplex (SimplicialCategory.sHom Y.unop X.unop))

/-- 概要：台の余錐から任意の Kan 対象への反変内部 Hom の錐。
方針：各脚の前合成を取り、元の余錐の自然性を反変に移す。
規約：頂点 c.pt 自体は Kan でなくてもよい。
使われ方：Kerodon 7.5.4.6、置換前の厳密な Hom の普遍性の検証。 -/
def underlyingKanCoconeHomCone (c : Cocone (F ⋙ kanObjectForget)) (X : KanObject.{u}ᵒᵖ) :
    Cone (simplicialHomDiagram F.op X) where
  pt := (ihom c.pt).obj X.unop.obj
  π :=
    { app := fun i ↦ (pre (c.ι.app i.unop)).app X.unop.obj
      naturality := by
        intro i j f
        change 𝟙 _ ≫ (pre (c.ι.app j.unop)).app X.unop.obj =
          (pre (c.ι.app i.unop)).app X.unop.obj ≫
            (pre ((F ⋙ kanObjectForget).map f.unop)).app X.unop.obj
        rw [Category.id_comp, ← NatTrans.comp_app, ← pre_map, c.w f.unop] }

/-- 概要：台の通常の余極限の内部 Hom 錐は全ての Kan 対象について極限。
方針：反変内部 Hom の極限保存を使い、係数図式の厳密な同型で表示を戻す。
規約：元の余極限頂点の Kan 性は不要。
使われ方：Kerodon 7.5.4.6、Kan 置換前の押し出しの Hom の普遍性。 -/
def underlyingKanCoconeHomCone_isLimit (c : Cocone (F ⋙ kanObjectForget))
    (hc : IsColimit c) (X : KanObject.{u}ᵒᵖ) : IsLimit (underlyingKanCoconeHomCone c X) := by
  let e : simplicialHomDiagram F.op X ≅
      (F ⋙ kanObjectForget).op ⋙ (internalHom (C := SSet.{u})).flip.obj X.unop.obj :=
    eqToIso (by
      unfold simplicialHomDiagram
      rw [kanObjectOppositeHomFunctor_eq X.unop]
      rfl)
  apply (IsLimit.postcomposeHomEquiv e _).toFun
  have hd := isLimitOfPreserves ((internalHom (C := SSet.{u})).flip.obj X.unop.obj) hc.op
  refine IsLimit.ofIsoLimit hd (Cone.ext (Iso.refl _) ?_)
  intro i
  simp only [Cone.postcompose_obj_π, NatTrans.comp_app, Iso.refl_hom, Category.id_comp]
  simp only [e, eqToIso.hom, eqToHom_refl]
  rfl

/-- 概要：台の余錐の頂点を anodyne な Kan 置換に替えた通常の Kan 複体の余錐。
方針：各脚を置換の単位で後合成する。
規約：元の図式 F の対象と射は保持する。
使われ方：HTT 4.2.4.1、実際の homotopy 余極限の Kan な余錐。 -/
def anodyneKanCocone (c : Cocone (F ⋙ kanObjectForget)) : Cocone F where
  pt := anodyneKanObject c.pt
  ι :=
    { app := fun i ↦ (show (F.obj i).obj ⟶ (anodyneKanObject c.pt).obj from
        c.ι.app i ≫ anodyneKanObjectUnit c.pt)
      naturality := by
        intro i j f
        change (F ⋙ kanObjectForget).map f ≫
          (c.ι.app j ≫ anodyneKanObjectUnit c.pt) = _
        rw [← Category.assoc, c.w f]
        change c.ι.app i ≫ anodyneKanObjectUnit c.pt =
          (c.ι.app i ≫ anodyneKanObjectUnit c.pt) ≫ 𝟙 (anodyneKanObject c.pt).obj
        exact (Category.comp_id _).symm }

/-- 概要：置換後の反変豊穣 Hom の錐から置換前の内部 Hom の錐への実際の射。
方針：置換の単位で前合成し、脚との可換性を内部 Hom の合成則で確認する。
規約：対象 X は任意の Kan 対象。
使われ方：Kerodon 7.5.4.6、通常の余極限から homotopy 余極限への比較。 -/
def anodyneKanCoconeHomComparison (c : Cocone (F ⋙ kanObjectForget)) (X : KanObject.{u}ᵒᵖ) :
    simplicialHomCone (anodyneKanCocone c).op X ⟶ underlyingKanCoconeHomCone c X where
  hom := (pre (anodyneKanObjectUnit c.pt)).app X.unop.obj
  w i := by
    change (pre (anodyneKanObjectUnit c.pt)).app X.unop.obj ≫
      (pre (c.ι.app i.unop)).app X.unop.obj =
        (pre (c.ι.app i.unop ≫ anodyneKanObjectUnit c.pt)).app X.unop.obj
    rw [pre_map, NatTrans.comp_app]

/-- 概要：置換前後の Hom 錐の比較射は単体的ホモトピー同値。
方針：置換の単位による前合成の trivial Kan fibration 性を使う。
規約：元の頂点の Kan 性は不要。
使われ方：HTT 4.2.4.1、Kan 置換後も Hom の homotopy 極限性を保持する。 -/
lemma anodyneKanCoconeHomComparison_homotopyEquivalence
    (c : Cocone (F ⋙ kanObjectForget)) (X : KanObject.{u}ᵒᵖ) :
    IsSimplicialHomotopyEquivalence (anodyneKanCoconeHomComparison c X).hom :=
  homotopyEquivalence_pre_of_anodyne _ (anodyneKanObjectUnit_anodyne c.pt) X.unop.obj

/-- 概要：再添字した置換後の反転 Hom 比較は置換前の比較と Hom の同値の合成に等しい。
方針：反転した錐の比較射に重み付き end の自然性を使い、恒等の係数写像を消す。
規約：G は任意の通常の再添字関手。
使われ方：Kerodon 7.5.4.6、押し出しの反変 Hom を標準 cospan として判定する主可換式。 -/
lemma anodyneKanCocone_reflectedComparison_factorization
    (c : Cocone (F ⋙ kanObjectForget)) (G : J ⥤ Iᵒᵖ) (X : KanObject.{u}ᵒᵖ) :
    reflectedRepresentableComparison ((anodyneKanCocone c).op.whisker G) X =
      SSet.opFunctor.map (anodyneKanCoconeHomComparison c X).hom ≫
        bousfieldKanConeComparison
          (SSet.opFunctor.mapCone ((underlyingKanCoconeHomCone c X).whisker G)) := by
  change weightedConeComparison (bousfieldKanWeight J)
      (SSet.opFunctor.mapCone ((simplicialHomCone (anodyneKanCocone c).op X).whisker G)) = _
  have h := weightedConeComparison_naturality (bousfieldKanWeight J)
    (SSet.opFunctor.mapCone ((simplicialHomCone (anodyneKanCocone c).op X).whisker G))
    (SSet.opFunctor.mapCone ((underlyingKanCoconeHomCone c X).whisker G))
    (SSet.opFunctor.map (anodyneKanCoconeHomComparison c X).hom) (𝟙 _)
    (fun j ↦ by
      change SSet.opFunctor.map (anodyneKanCoconeHomComparison c X).hom ≫
        SSet.opFunctor.map ((underlyingKanCoconeHomCone c X).π.app (G.obj j)) = _
      rw [← CategoryTheory.Functor.map_comp, (anodyneKanCoconeHomComparison c X).w]
      simp only [NatTrans.id_app, Category.comp_id]
      rfl)
  simpa only [bousfieldKanConeComparison, weightedSectionsMap_id, Category.comp_id] using h.symm

/-- 概要：Kan 置換した余錐の native な余極限性は置換前の Hom 錐の反転 end 比較で判定できる。
方針：添字の同型と一般の反転判定を使い、単位による Hom の同値を合成から消去する。
規約：置換前の余錐の頂点が Kan であることを仮定しない。
使われ方：HTT 4.2.4.1、実際の homotopy 押し出しの普遍性への移送。 -/
lemma anodyneKanCocone_isColimit_iff_reflectedHomComparison
    (c : Cocone (F ⋙ kanObjectForget)) (G : J ⥤ Iᵒᵖ)
    [IsIso ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap G))] :
    IsColimitCone (strictNativeCocone (anodyneKanCocone c)) ↔ ∀ X : KanObject.{u}ᵒᵖ,
      IsSimplicialHomotopyEquivalence (bousfieldKanConeComparison
        (SSet.opFunctor.mapCone ((underlyingKanCoconeHomCone c X).whisker G))) := by
  rw [strictNativeCocone_isColimit_iff,
    strictCoherentCone_isLimit_iff_whisker _ G,
    strictCoherentCone_isLimit_iff_reflectedRepresentableComparison]
  apply forall_congr'
  intro X
  rw [anodyneKanCocone_reflectedComparison_factorization]
  have : KanComplex (simplicialHomCone (anodyneKanCocone c).op X).pt :=
    inferInstanceAs (KanComplex ((ihom (anodyneKanObject c.pt).obj).obj X.unop.obj))
  have : KanComplex (underlyingKanCoconeHomCone c X).pt :=
    inferInstanceAs (KanComplex ((ihom c.pt).obj X.unop.obj))
  have : ∀ j, KanComplex (((G ⋙ simplicialHomDiagram F.op X) ⋙ SSet.opFunctor).obj j) :=
    fun j ↦ inferInstanceAs
      (KanComplex (SimplicialCategory.sHom (F.obj (G.obj j).unop) X.unop).op)
  have := bousfieldKanHolim_kanComplex ((G ⋙ simplicialHomDiagram F.op X) ⋙ SSet.opFunctor)
  have : ∀ j, KanComplex ((simplicialHomDiagram (G ⋙ F.op) X ⋙ SSet.opFunctor).obj j) :=
    fun j ↦ inferInstanceAs
      (KanComplex (SimplicialCategory.sHom (F.obj (G.obj j).unop) X.unop).op)
  have := bousfieldKanHolim_kanComplex (simplicialHomDiagram (G ⋙ F.op) X ⋙ SSet.opFunctor)
  have he := oppositeKanHomotopyEquivalence
    (anodyneKanCoconeHomComparison_homotopyEquivalence c X)
  exact ⟨fun h ↦ he.cancel_left h, fun h ↦ he.comp h⟩

end
end SerrePositivity.InfinityCategories.HomotopyLimits
