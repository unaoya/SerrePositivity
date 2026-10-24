module
public import SerrePositivity.EInfinity.FrameHom.FrameArrowAugmentationLimits
public import SerrePositivity.InfinityCategories.F1B.Homotopy.HomotopyWhiskering
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.EnrichedPostcomposition
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.EnrichedPrecomposition
public import SerrePositivity.InfinityCategories.F1B.NerveComparison.NatTransWhiskering
/-! 概要：同じ通常列の全屋根は、反転関手の全自然同型に自然である。
方針：既存 QCat 双圏の交換則と関手の合成保存から通常列の全交換式を導く。
規約：元の全図式・augmentation・評価と同じ反転射を保持する。
使われ方：実 U の局所化源比較を元の複体屋根へ接続する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.FrameHom.NerveColumn
open CategoryTheory SSet MonoidalClosed
open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel
open scoped Simplicial
variable {I C : Type u} [Category.{u} I] [Category.{u} C]
  {E : SSet.{u}} [Quasicategory E]

/-- 概要：元の通常自然変換の全関手圏での像。
方針：同じ nerve の全射を後合成する。
規約：元の円柱を保持。使われ方：全屋根の二本の脚。 -/
def hom (F : nerve C ⟶ E) {V W : I ⥤ C} (a : V ⟶ W) :
    FunctorHom (nerveMap V ≫ F) (nerveMap W ≫ F) :=
  (hoFunctor.map ((ihom (nerve I)).map F)).toFunctor.map (F1B.nerveNatTransHom a)

omit [Quasicategory E] in
/-- 概要：元の全通常変換の像は同じ通常後合成で回収される。
方針：既存の nerve 自然変換の後合成式を使う。
規約：全図式を保持。使われ方：元の忘却像の全回収。 -/
lemma hom_whiskerRight {D : Type u} [Category.{u} D] (H : C ⥤ D)
    (F : nerve D ⟶ E) {V W : I ⥤ C} (a : V ⟶ W) :
    hom (nerveMap H ≫ F) a = hom F (Functor.whiskerRight a H) := by
  unfold hom
  rw [← F1B.nerveNatTransHom_whiskerRight a H]
  have h₁ := Functor.map_comp (ihom (nerve I)) (nerveMap H) F
  have h₂ := Functor.map_comp hoFunctor ((ihom (nerve I)).map (nerveMap H))
    ((ihom (nerve I)).map F)
  have h : (hoFunctor.map ((ihom (nerve I)).map (nerveMap H ≫ F))).toFunctor =
      (hoFunctor.map ((ihom (nerve I)).map (nerveMap H))).toFunctor ⋙
        (hoFunctor.map ((ihom (nerve I)).map F)).toFunctor := by
    rw [h₁]
    exact congrArg Cat.Hom.toFunctor h₂
  simpa only [Functor.comp_map, eqToHom_refl, Category.id_comp, Category.comp_id] using
    Functor.congr_hom h (F1B.nerveNatTransHom a)

/-- 概要：元の弱 augmentation の全像は同じ全関手同型。
方針：元の全円柱の成分反転を使う。
規約：指定自然変換自身を保持。使われ方：元の屋根の左脚の反転。 -/
def augmentationIso (F : nerve C ⟶ E) (V : I ⥤ C) {X : C}
    (p : V ⟶ (Functor.const I).obj X)
    (hp : ∀ i, IsInvertibleEdge ((nerve.edgeMk (p.app i)).map F).toTruncated) :
    FunctorIso (nerveMap V ≫ F) (nerveMap ((Functor.const I).obj X) ≫ F) := by
  apply functorIsoOfPointwiseInvertibleHomotopy
    (functorHomotopyPostcomp (F1B.nerveNatTransHomotopy p) F)
  intro z
  obtain ⟨i, rfl⟩ := ComposableArrows.mk₀_surjective z
  have he : (simplicialHomotopyVertexEdge
      (functorHomotopyPostcomp (F1B.nerveNatTransHomotopy p) F) (nerveVertex i)).edge =
      ((nerve.edgeMk (p.app i)).map F).edge := by
    exact congrArg (F.app (Opposite.op ⦋1⦌)) (F1B.nerveNatTransHomotopy_component p i)
  exact (isInvertibleEdge_congr he).mpr (hp i)

/-- 概要：指定した全同型の順射は元の augmentation の全像。
方針：同じ後合成円柱の式を使う。
規約：元の全射を保持。使われ方：全屋根のキャンセル。 -/
lemma augmentationIso_hom (F : nerve C ⟶ E) (V : I ⥤ C) {X : C}
    (p : V ⟶ (Functor.const I).obj X)
    (hp : ∀ i, IsInvertibleEdge ((nerve.edgeMk (p.app i)).map F).toTruncated) :
    (augmentationIso F V p hp).hom = hom F p := by
  change Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
    (functorHomotopyPostcomp (F1B.nerveNatTransHomotopy p) F)) = _
  rw [functorHomotopyPostcomp_hom]
  have hb : Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy (F1B.nerveNatTransHomotopy p)) =
      F1B.nerveNatTransHom p := F1B.nerveNatTransHomotopy_hom p
  rw [hb]
  rfl

/-- 概要：全自然変換の像は元の後続自然同型に自然。
方針：全関手圏の交換則へ元の二射を代入する。
規約：全図式を保持。使われ方：元の屋根の二つの正方形。 -/
lemma hom_naturality {F G : nerve C ⟶ E} (e : FunctorIso F G)
    {V W : I ⥤ C} (a : V ⟶ W) :
    hom F a ≫ (e.precomp (nerveMap W)).hom =
      (e.precomp (nerveMap V)).hom ≫ hom G a := by
  let α := (qcatCellEquiv (nerveMap V) (nerveMap W)).symm (F1B.nerveNatTransHom a)
  let β := (qcatCellEquiv F G).symm e.hom
  have h := congrArg (qcatCellEquiv (nerveMap V ≫ F) (nerveMap W ≫ G))
    (Bicategory.whisker_exchange α β).symm
  change qcatCellEquiv _ _ (Bicategory.whiskerRight α (qcatMap F)) ≫
      qcatCellEquiv _ _ (Bicategory.whiskerLeft (qcatMap (nerveMap W)) β) =
    qcatCellEquiv _ _ (Bicategory.whiskerLeft (qcatMap (nerveMap V)) β) ≫
      qcatCellEquiv _ _ (Bicategory.whiskerRight α (qcatMap G)) at h
  rw [qcatCell_whiskerRight, qcatCell_whiskerLeft,
    qcatCell_whiskerLeft, qcatCell_whiskerRight] at h
  have heV : (e.precomp (nerveMap V)).hom =
      (hoFunctor.map ((pre (nerveMap V)).app E)).toFunctor.map e.hom := rfl
  have heW : (e.precomp (nerveMap W)).hom =
      (hoFunctor.map ((pre (nerveMap W)).app E)).toFunctor.map e.hom := rfl
  rw [heV, heW]
  simpa only [α, β, Equiv.apply_symm_apply, hom] using h

/-- 概要：元の全屋根は同じ後続自然同型と可換。
方針：元の左右脚の全交換式から左脚を反転する。
規約：同じ全添字と元の左右脚を保持。使われ方：U の全源比較。 -/
lemma roof_naturality {F G : nerve C ⟶ E} (e : FunctorIso F G)
    (V : I ⥤ C) {X Y : C} (p : V ⟶ (Functor.const I).obj X)
    (hpF : ∀ i, IsInvertibleEdge ((nerve.edgeMk (p.app i)).map F).toTruncated)
    (hpG : ∀ i, IsInvertibleEdge ((nerve.edgeMk (p.app i)).map G).toTruncated)
    (s : V ⟶ (Functor.const I).obj Y) :
    (e.precomp (nerveMap ((Functor.const I).obj X))).hom ≫
      (augmentationIso G V p hpG).inv ≫ hom G s =
    (augmentationIso F V p hpF).inv ≫ hom F s ≫
      (e.precomp (nerveMap ((Functor.const I).obj Y))).hom := by
  apply (cancel_epi (augmentationIso F V p hpF).hom).mp
  have hp := hom_naturality e p
  rw [← augmentationIso_hom F V p hpF, ← augmentationIso_hom G V p hpG] at hp
  calc
    _ = ((augmentationIso F V p hpF).hom ≫
        (e.precomp (nerveMap ((Functor.const I).obj X))).hom) ≫
        (augmentationIso G V p hpG).inv ≫ hom G s := by simp only [Category.assoc]
    _ = (e.precomp (nerveMap V)).hom ≫ hom G s := by
      rw [hp]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = hom F s ≫ (e.precomp (nerveMap ((Functor.const I).obj Y))).hom :=
      (hom_naturality e s).symm
    _ = _ := by simp only [Iso.hom_inv_id_assoc]

end SerrePositivity.EInfinity.FrameHom.NerveColumn
