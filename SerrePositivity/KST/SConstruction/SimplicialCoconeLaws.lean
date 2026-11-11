module
public import SerrePositivity.KST.SConstruction.EnrichedCoconeFamily

/-! # 全余錐成分で検出する候補 Hom 作用の恒等・合成
概要：元の豊穣関手からの余錐成分に自然な候補作用の、制限後の恒等・合成を証明する。
方針：通常の豊穣結合律と中間射交換を使う。
規約：候補作用の関手性を仮定しない。使われ方：押し出しの厳密豊穣関手。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
variable {C : Type v} [EnrichedCategory SSet.{u} C]
  {D : Type w} [Category.{u} D] [SimplicialCategory D]

/-- 元の豊穣関手からの余錐に自然な候補作用は、その成分で恒等律を満たす。 -/
lemma simplicialCocone_map_id (F : EnrichedFunctor SSet.{u} C D) (X : C) (Q : D)
    (m : (X ⟶[SSet.{u}] X) ⟶ (Q ⟶[SSet.{u}] Q)) (j : F.obj X ⟶ Q)
    (h : m ≫ eHomWhiskerRight SSet j Q = F.map X X ≫ eHomWhiskerLeft SSet (F.obj X) j) :
    (eId SSet X ≫ m) ≫ eHomWhiskerRight SSet j Q =
      eId SSet Q ≫ eHomWhiskerRight SSet j Q := by
  rw [Category.assoc, h, ← Category.assoc, F.map_id]
  exact simplicialIdentity_whisker j

/-- 二つの候補作用が同じ余錐に自然なら、その合成も同じ制限で比較できる。 -/
lemma simplicialCocone_map_comp (F : EnrichedFunctor SSet.{u} C D) (X Y Z : C)
    (QX QY QZ : D) (jX : F.obj X ⟶ QX) (jY : F.obj Y ⟶ QY) (jZ : F.obj Z ⟶ QZ)
    (mXY : (X ⟶[SSet.{u}] Y) ⟶ (QX ⟶[SSet.{u}] QY))
    (mYZ : (Y ⟶[SSet.{u}] Z) ⟶ (QY ⟶[SSet.{u}] QZ))
    (hXY : mXY ≫ eHomWhiskerRight SSet jX QY =
      F.map X Y ≫ eHomWhiskerLeft SSet (F.obj X) jY)
    (hYZ : mYZ ≫ eHomWhiskerRight SSet jY QZ =
      F.map Y Z ≫ eHomWhiskerLeft SSet (F.obj Y) jZ) :
    ((mXY ⊗ₘ mYZ) ≫ eComp SSet QX QY QZ) ≫ eHomWhiskerRight SSet jX QZ =
      (eComp SSet X Y Z ≫ F.map X Z) ≫ eHomWhiskerLeft SSet (F.obj X) jZ := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.enriched_compatible_comp SSet (EnrichedFunctor.id SSet.{u} D)
    jX jY jZ (F.map X Y) mXY (F.map Y Z) mYZ
    (by
      change mXY ≫ eHomWhiskerRight SSet jX QY =
        F.map X Y ≫ 𝟙 (F.obj X ⟶[SSet.{u}] F.obj Y) ≫
          eHomWhiskerLeft SSet (F.obj X) jY
      rw [Category.id_comp]
      exact hXY)
    (by
      change mYZ ≫ eHomWhiskerRight SSet jY QZ =
        F.map Y Z ≫ 𝟙 (F.obj Y ⟶[SSet.{u}] F.obj Z) ≫
          eHomWhiskerLeft SSet (F.obj Y) jZ
      rw [Category.id_comp]
      exact hYZ)
  change (mXY ⊗ₘ mYZ) ≫ eComp SSet QX QY QZ ≫ eHomWhiskerRight SSet jX QZ =
    (F.map X Y ⊗ₘ F.map Y Z) ≫ eComp SSet (F.obj X) (F.obj Y) (F.obj Z) ≫
      𝟙 _ ≫ eHomWhiskerLeft SSet (F.obj X) jZ at h
  rw [Category.id_comp, ← Category.assoc (F.map X Y ⊗ₘ F.map Y Z),
    ← F.map_comp X Y Z] at h
  simpa only [Category.assoc] using h

end SerrePositivity.KST.SConstruction
