module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanSourceReplacement
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.StrictConeReindex
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.GeneralReflectedCriterion

/-!
概要：台の通常の余錐の頂点を Kan 置換し、全反変 Hom と native な余極限性を比較する。
方針：置換の単位による内部 Hom の前合成を錐の射とし、反転 end の比較を厳密に分解する。
規約：元の余錐の頂点の Kan 性や余極限性は構成に要求しない。
使われ方：HTT 4.2.4.1、通常の押し出しから実際の homotopy 押し出しへの移送。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
noncomputable section
variable {I J : Type u} [SmallCategory I] [SmallCategory J]
  {F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}}

local instance anodyneCoconeOppositeHomKan (X Y : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}ᵒᵖ) :
    KanComplex (SimplicialCategory.sHom X Y) :=
  inferInstanceAs (KanComplex (SimplicialCategory.sHom Y.unop X.unop))

/-- 概要：台の余錐から任意の Kan 対象への反変内部 Hom の錐。
方針：各脚の前合成を取り、元の余錐の自然性を反変に移す。
規約：頂点 c.pt 自体は Kan でなくてもよい。
使われ方：Kerodon 7.5.4.6（Tag 03BB）、置換前の厳密な Hom の普遍性の検証。 -/
def underlyingKanCoconeHomCone (c : Cocone (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)) (X : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}ᵒᵖ) :
    Cone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F.op X) where
  pt := (ihom c.pt).obj X.unop.obj
  π :=
    { app := fun i ↦ (pre (c.ι.app i.unop)).app X.unop.obj
      naturality := by
        intro i j f
        change 𝟙 _ ≫ (pre (c.ι.app j.unop)).app X.unop.obj =
          (pre (c.ι.app i.unop)).app X.unop.obj ≫
            (pre ((F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget).map f.unop)).app X.unop.obj
        rw [Category.id_comp, ← NatTrans.comp_app, ← pre_map, c.w f.unop] }

/-- 概要：台の通常の余極限の内部 Hom 錐は全ての Kan 対象について極限。
方針：反変内部 Hom の極限保存を使い、係数図式の厳密な同型で表示を戻す。
規約：元の余極限頂点の Kan 性は不要。
使われ方：Kerodon 7.5.4.6（Tag 03BB）、Kan 置換前の押し出しの Hom の普遍性。 -/
def underlyingKanCoconeHomCone_isLimit (c : Cocone (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget))
    (hc : IsColimit c) (X : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}ᵒᵖ) : IsLimit (underlyingKanCoconeHomCone c X) := by
  let e : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F.op X ≅
      (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget).op ⋙ (internalHom (C := SSet.{u})).flip.obj X.unop.obj :=
    eqToIso (by
      unfold _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanObjectOppositeHomFunctor_eq X.unop]
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
def anodyneKanCocone (c : Cocone (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)) : Cocone F where
  pt := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.anodyneKanObject c.pt
  ι :=
    { app := fun i ↦ (show (F.obj i).obj ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.anodyneKanObject c.pt).obj from
        c.ι.app i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.anodyneKanObjectUnit c.pt)
      naturality := by
        intro i j f
        change (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget).map f ≫
          (c.ι.app j ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.anodyneKanObjectUnit c.pt) = _
        rw [← Category.assoc, c.w f]
        change c.ι.app i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.anodyneKanObjectUnit c.pt =
          (c.ι.app i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.anodyneKanObjectUnit c.pt) ≫ 𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.anodyneKanObject c.pt).obj
        exact (Category.comp_id _).symm }

/-- 概要：置換後の反変豊穣 Hom の錐から置換前の内部 Hom の錐への実際の射。
方針：置換の単位で前合成し、脚との可換性を内部 Hom の合成則で確認する。
規約：対象 X は任意の Kan 対象。
使われ方：Kerodon 7.5.4.6（Tag 03BB）、通常の余極限から homotopy 余極限への比較。 -/
def anodyneKanCoconeHomComparison (c : Cocone (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)) (X : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}ᵒᵖ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomCone (anodyneKanCocone c).op X ⟶ underlyingKanCoconeHomCone c X where
  hom := (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.anodyneKanObjectUnit c.pt)).app X.unop.obj
  w i := by
    change (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.anodyneKanObjectUnit c.pt)).app X.unop.obj ≫
      (pre (c.ι.app i.unop)).app X.unop.obj =
        (pre (c.ι.app i.unop ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.anodyneKanObjectUnit c.pt)).app X.unop.obj
    rw [pre_map, NatTrans.comp_app]

/-- 概要：置換前後の Hom 錐の比較射は単体的ホモトピー同値。
方針：置換の単位による前合成の trivial Kan fibration 性を使う。
規約：元の頂点の Kan 性は不要。
使われ方：HTT 4.2.4.1、Kan 置換後も Hom の homotopy 極限性を保持する。 -/
lemma anodyneKanCoconeHomComparison_homotopyEquivalence
    (c : Cocone (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)) (X : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}ᵒᵖ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (anodyneKanCoconeHomComparison c X).hom :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.homotopyEquivalence_pre_of_anodyne _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.anodyneKanObjectUnit_anodyne c.pt) X.unop.obj

/-- 概要：再添字した置換後の反転 Hom 比較は置換前の比較と Hom の同値の合成に等しい。
方針：反転した錐の比較射に重み付き end の自然性を使い、恒等の係数写像を消す。
規約：G は任意の通常の再添字関手。
使われ方：Kerodon 7.5.4.6（Tag 03BB）、押し出しの反変 Hom を標準 cospan として判定する主可換式。 -/
lemma anodyneKanCocone_reflectedComparison_factorization
    (c : Cocone (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)) (G : J ⥤ Iᵒᵖ) (X : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}ᵒᵖ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedRepresentableComparison ((anodyneKanCocone c).op.whisker G) X =
      SSet.opFunctor.map (anodyneKanCoconeHomComparison c X).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison
          (SSet.opFunctor.mapCone ((underlyingKanCoconeHomCone c X).whisker G)) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight J)
      (SSet.opFunctor.mapCone ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomCone (anodyneKanCocone c).op X).whisker G)) = _
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison_naturality (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight J)
    (SSet.opFunctor.mapCone ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomCone (anodyneKanCocone c).op X).whisker G))
    (SSet.opFunctor.mapCone ((underlyingKanCoconeHomCone c X).whisker G))
    (SSet.opFunctor.map (anodyneKanCoconeHomComparison c X).hom) (𝟙 _)
    (fun j ↦ by
      change SSet.opFunctor.map (anodyneKanCoconeHomComparison c X).hom ≫
        SSet.opFunctor.map ((underlyingKanCoconeHomCone c X).π.app (G.obj j)) = _
      rw [← CategoryTheory.Functor.map_comp, (anodyneKanCoconeHomComparison c X).w]
      simp only [NatTrans.id_app, Category.comp_id]
      rfl)
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap_id, Category.comp_id] using h.symm

/-- 概要：Kan 置換した余錐の native な余極限性は置換前の Hom 錐の反転 end 比較で判定できる。
方針：添字の同型と一般の反転判定を使い、単位による Hom の同値を合成から消去する。
規約：置換前の余錐の頂点が Kan であることを仮定しない。
使われ方：HTT 4.2.4.1、実際の homotopy 押し出しの普遍性への移送。 -/
lemma anodyneKanCocone_isColimit_iff_reflectedHomComparison
    (c : Cocone (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)) (G : J ⥤ Iᵒᵖ)
    [IsIso ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap G))] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictNativeCocone (anodyneKanCocone c)) ↔ ∀ X : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}ᵒᵖ,
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison
        (SSet.opFunctor.mapCone ((underlyingKanCoconeHomCone c X).whisker G))) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictNativeCocone_isColimit_iff,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone_isLimit_iff_whisker _ G,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone_isLimit_iff_reflectedRepresentableComparison]
  apply forall_congr'
  intro X
  rw [anodyneKanCocone_reflectedComparison_factorization]
  have : KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomCone (anodyneKanCocone c).op X).pt :=
    inferInstanceAs (KanComplex ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.anodyneKanObject c.pt).obj).obj X.unop.obj))
  have : KanComplex (underlyingKanCoconeHomCone c X).pt :=
    inferInstanceAs (KanComplex ((ihom c.pt).obj X.unop.obj))
  have : ∀ j, KanComplex (((G ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F.op X) ⋙ SSet.opFunctor).obj j) :=
    fun j ↦ inferInstanceAs
      (KanComplex (SimplicialCategory.sHom (F.obj (G.obj j).unop) X.unop).op)
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim_kanComplex ((G ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F.op X) ⋙ SSet.opFunctor)
  have : ∀ j, KanComplex ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (G ⋙ F.op) X ⋙ SSet.opFunctor).obj j) :=
    fun j ↦ inferInstanceAs
      (KanComplex (SimplicialCategory.sHom (F.obj (G.obj j).unop) X.unop).op)
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim_kanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (G ⋙ F.op) X ⋙ SSet.opFunctor)
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.oppositeKanHomotopyEquivalence
    (anodyneKanCoconeHomComparison_homotopyEquivalence c X)
  exact ⟨fun h ↦ he.cancel_left h, fun h ↦ he.comp h⟩

end
end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
