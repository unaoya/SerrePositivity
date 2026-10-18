module

public import SerrePositivity.KST.Spectra.PointedWeightedEndFunctor

/-!
概要：点つき enriched end の重みの射に関する反変関手性。
方針：自由基点を加えた重みの射で各内部 Hom を前合成し、end へ持ち上げる。
規約：重みも係数も同じ小圏上の共変図式。
使われ方：Goerss–Jardine VIII §§1–2、HA §1.4.2。群作用の余単体 cochain 模型の構造射。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed SSet Opposite
open scoped MonoidalClosed

namespace SerrePositivity.KST.Spectra.PointedWeightedEnd

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance weightedEndPreMapSelfEnrichment : EnrichedOrdinaryCategory SSet.{u} SSet.{u} :=
  enrichedOrdinaryCategorySelf SSet.{u}

local instance weightedEndPreMapPointedSelfEnrichment :
    EnrichedOrdinaryCategory PointedSimplicialSet.{u} PointedSimplicialSet.{u} :=
  enrichedOrdinaryCategorySelf PointedSimplicialSet.{u}

variable {I : Type u} [SmallCategory I]

/-- 概要：重みの自然変換が点つき end に誘導する前合成の射。
方針：各成分の前合成を end の射影に続ける。
規約：自然変換 W → V から end(V,D) → end(W,D) を得る。
使われ方：Goerss–Jardine VIII §2。作用の cochain の次数を変える射。 -/
def preMap {W V : I ⥤ SSet.{u}} (θ : W ⟶ V) (D : I ⥤ PointedSimplicialSet.{u}) :
    obj V D ⟶ obj W D :=
  end_.lift (fun i ↦ end_.π (diagram V D) i ≫
    (pre (PointedObject.adjoinFunctor.map (θ.app i))).app (D.obj i)) (fun i j f ↦ by
      change (end_.π (diagram V D) i ≫
          (pre (PointedObject.adjoinFunctor.map (θ.app i))).app (D.obj i)) ≫
            eHomWhiskerLeft PointedSimplicialSet.{u}
              (PointedObject.adjoin (W.obj i)) (D.map f) =
        (end_.π (diagram V D) j ≫
          (pre (PointedObject.adjoinFunctor.map (θ.app j))).app (D.obj j)) ≫
            eHomWhiskerRight PointedSimplicialSet.{u}
              (PointedObject.adjoinFunctor.map (W.map f)) (D.obj j)
      rw [enrichedOrdinaryCategorySelf_eHomWhiskerLeft,
        enrichedOrdinaryCategorySelf_eHomWhiskerRight, Category.assoc]
      erw [pre_comm_ihom_map]
      rw [← Category.assoc]
      erw [π_condition V D f]
      rw [Category.assoc, Category.assoc]
      apply congrArg (fun t ↦ end_.π (diagram V D) j ≫ t)
      rw [← NatTrans.comp_app, ← pre_map, ← NatTrans.comp_app, ← pre_map,
        ← CategoryTheory.Functor.map_comp, ← θ.naturality f,
        CategoryTheory.Functor.map_comp])

@[reassoc (attr := simp)]
lemma preMap_π {W V : I ⥤ SSet.{u}} (θ : W ⟶ V)
    (D : I ⥤ PointedSimplicialSet.{u}) (i : I) :
    preMap θ D ≫ end_.π (diagram W D) i = end_.π (diagram V D) i ≫
      (pre (PointedObject.adjoinFunctor.map (θ.app i))).app (D.obj i) :=
  end_.lift_π _ _ i

/-- 概要：重みの恒等自然変換の前合成は恒等射。
方針：各射影で内部 Hom の恒等前合成を使う。
規約：点つき射の厳密な等式。
使われ方：Goerss–Jardine VIII §2。余単体構造の恒等法則。 -/
lemma preMap_id (W : I ⥤ SSet.{u}) (D : I ⥤ PointedSimplicialSet.{u}) :
    preMap (𝟙 W) D = 𝟙 (obj W D) := by
  apply end_.hom_ext
  intro i
  rw [preMap_π]
  simp only [NatTrans.id_app, CategoryTheory.Functor.map_id, pre_id, NatTrans.id_app,
    Category.id_comp]
  erw [Category.comp_id]

/-- 概要：重みの自然変換の合成は前合成の逆順の合成。
方針：各射影で内部 Hom の前合成の合成則を使う。
規約：自然変換の向きと end の射の向きが逆になる。
使われ方：Goerss–Jardine VIII §2。余単体構造の合成法則。 -/
lemma preMap_comp {W V U : I ⥤ SSet.{u}} (θ : W ⟶ V) (υ : V ⟶ U)
    (D : I ⥤ PointedSimplicialSet.{u}) :
    preMap (θ ≫ υ) D = preMap υ D ≫ preMap θ D := by
  apply end_.hom_ext
  intro i
  rw [preMap_π, Category.assoc, preMap_π, ← Category.assoc, preMap_π,
    NatTrans.comp_app, CategoryTheory.Functor.map_comp, pre_map, NatTrans.comp_app,
    Category.assoc]

/-- 概要：固定した係数への点つき end は重みの図式に反変な関手。
方針：重みの前合成と厳密な関手法則を束ねる。
規約：通常の圏の反対圏を源にする。
使われ方：Goerss–Jardine VIII §§1–2。単体的な重みから余単体係数を作る。 -/
def weightFunctor (D : I ⥤ PointedSimplicialSet.{u}) :
    (I ⥤ SSet.{u})ᵒᵖ ⥤ PointedSimplicialSet.{u} where
  obj W := obj W.unop D
  map f := preMap f.unop D
  map_id W := preMap_id W.unop D
  map_comp f g := preMap_comp g.unop f.unop D

end

end SerrePositivity.KST.Spectra.PointedWeightedEnd
