module

public import SerrePositivity.InfinityCategories.HomotopyLimits.ReflectedWeightedHomPostcomposition
public import SerrePositivity.InfinityCategories.HomotopyLimits.BousfieldKanCoherentCocone

/-!
概要：Kan 置換済み Bousfield–Kan coend の反転 Hom 比較の豊穣自然性。
方針：反転重みの end の作用を既存の反変豊穣 Hom 図式の end へ移す。
規約：既存の比較そのものと照合し、coherent 余錐の普遍性とは区別する。
使われ方：HTT 4.2.4.1 の普遍切断点から実際の比較族を復元する代数的入力。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {I : Type u} [SmallCategory I]

/-- coend の反変 Hom 図式を既存の Kan 対象の豊穣 Hom 図式へ移す end 同型。 -/
def kanReflectedBousfieldKanEndIso (F : I ⥤ KanObject.{u}) (Y : KanObject.{u}) :
    weightedSections (bousfieldKanWeight Iᵒᵖ)
        (weightedColimitHomDiagram (F ⋙ kanObjectForget) Y.obj ⋙ SSet.opFunctor) ≅
      bousfieldKanHolim (simplicialHomDiagram F.op (Opposite.op Y) ⋙ SSet.opFunctor) :=
  eqToIso (congrArg (fun D ↦ bousfieldKanHolim (D ⋙ SSet.opFunctor))
    (kanBousfieldKanColimitHomDiagram_eq F Y))

/-- 既存の反転 Hom の end に対する Hom(Y,Z).op 全体の後合成。 -/
def kanReflectedBousfieldKanEndPostcomposition
    (F : I ⥤ KanObject.{u}) (Y Z : KanObject.{u}) :
    bousfieldKanHolim (simplicialHomDiagram F.op (Opposite.op Y) ⋙ SSet.opFunctor) ⊗
        (SimplicialCategory.sHom Y Z).op ⟶
      bousfieldKanHolim (simplicialHomDiagram F.op (Opposite.op Z) ⋙ SSet.opFunctor) :=
  ((kanReflectedBousfieldKanEndIso F Y).inv ▷ (SimplicialCategory.sHom Y Z).op) ≫
    reflectedWeightedHomPostcomposition (bousfieldKanWeight Iᵒᵖ)
      (F ⋙ kanObjectForget) Y.obj Z.obj ≫ (kanReflectedBousfieldKanEndIso F Z).hom

/-- Kan 置換後の既存の比較は反転 Hom 空間全体の後合成を保つ。 -/
lemma kanReflectedBousfieldKanColimitHomComparison_enriched_naturality
    (F : I ⥤ KanObject.{u}) (Y Z : KanObject.{u}) :
    (Functor.Monoidal.μIso SSet.opFunctor
        (SimplicialCategory.sHom (kanReflectedBousfieldKanColimitObject F) Y)
        (SimplicialCategory.sHom Y Z)).hom ≫
      SSet.opFunctor.map (MonoidalClosed.comp
        (kanReflectedBousfieldKanColimitObject F).obj Y.obj Z.obj) ≫
        kanReflectedBousfieldKanColimitHomComparison F Z =
      (kanReflectedBousfieldKanColimitHomComparison F Y ▷ (SimplicialCategory.sHom Y Z).op) ≫
        kanReflectedBousfieldKanEndPostcomposition F Y Z := by
  dsimp only [SimplicialCategory.sHom, kanObject_simplicialCategory,
    kanObject_enrichedCategory]
  dsimp only [kanReflectedBousfieldKanColimitHomComparison,
    kanReflectedBousfieldKanColimitUnderlyingHomIso, Iso.trans_hom,
    kanReflectedBousfieldKanEndPostcomposition, kanReflectedBousfieldKanEndIso]
  simp only [comp_whiskerRight_assoc]
  rw [← comp_whiskerRight_assoc (eqToIso _).hom]
  rw [Iso.hom_inv_id, MonoidalCategory.id_whiskerRight, Category.id_comp]
  have h := reflectedWeightedColimitHomComparison_pre_enriched_naturality
    (bousfieldKanWeight Iᵒᵖ) (F ⋙ kanObjectForget)
    (anodyneKanObjectUnit (reflectedBousfieldKanColimit (F ⋙ kanObjectForget))) Y.obj Z.obj
  have h' := congrArg (fun m ↦ m ≫ (kanReflectedBousfieldKanEndIso F Z).hom) h
  simp only [comp_whiskerRight_assoc, Category.assoc] at h'
  convert h' using 1 <;> rfl

/-- Kan 置換射そのものに対応する既存の反転 Hom の end の普遍切断点。 -/
def kanReflectedBousfieldKanColimitHomPoint (F : I ⥤ KanObject.{u}) :
    𝟙_ SSet.{u} ⟶ bousfieldKanHolim
      (simplicialHomDiagram F.op (Opposite.op (kanReflectedBousfieldKanColimitObject F)) ⋙
        SSet.opFunctor) :=
  reflectedWeightedColimitHomPointOfMap (bousfieldKanWeight Iᵒᵖ)
    (F ⋙ kanObjectForget)
    (anodyneKanObjectUnit (reflectedBousfieldKanColimit (F ⋙ kanObjectForget))) ≫
      (kanReflectedBousfieldKanEndIso F (kanReflectedBousfieldKanColimitObject F)).hom

/-- 置換後の Hom 比較も、その普遍切断点への豊穣後合成から復元できる。 -/
lemma kanReflectedBousfieldKanColimitHomComparison_of_point
    (F : I ⥤ KanObject.{u}) (Y : KanObject.{u}) :
    (λ_ (SimplicialCategory.sHom (kanReflectedBousfieldKanColimitObject F) Y).op).inv ≫
        (kanReflectedBousfieldKanColimitHomPoint F ▷
          (SimplicialCategory.sHom (kanReflectedBousfieldKanColimitObject F) Y).op) ≫
          kanReflectedBousfieldKanEndPostcomposition F
            (kanReflectedBousfieldKanColimitObject F) Y =
      kanReflectedBousfieldKanColimitHomComparison F Y := by
  dsimp only [SimplicialCategory.sHom, kanObject_simplicialCategory,
    kanObject_enrichedCategory]
  dsimp only [kanReflectedBousfieldKanColimitHomPoint,
    kanReflectedBousfieldKanEndPostcomposition,
    kanReflectedBousfieldKanColimitHomComparison,
    kanReflectedBousfieldKanColimitUnderlyingHomIso, Iso.trans_hom]
  simp only [comp_whiskerRight_assoc]
  rw [← comp_whiskerRight_assoc
    (kanReflectedBousfieldKanEndIso F (kanReflectedBousfieldKanColimitObject F)).hom]
  rw [Iso.hom_inv_id, MonoidalCategory.id_whiskerRight, Category.id_comp]
  have h := reflectedWeightedColimitHomComparison_pre_of_point
    (bousfieldKanWeight Iᵒᵖ) (F ⋙ kanObjectForget)
    (anodyneKanObjectUnit (reflectedBousfieldKanColimit (F ⋙ kanObjectForget))) Y.obj
  have h' := congrArg (fun m ↦ m ≫ (kanReflectedBousfieldKanEndIso F Y).hom) h
  simp only [Category.assoc] at h'
  convert h' using 1 <;> rfl

/-- end の普遍切断点は、既存の比較による恒等射の像そのもの。 -/
lemma kanReflectedBousfieldKanColimitHomPoint_eq
    (F : I ⥤ KanObject.{u}) :
    kanReflectedBousfieldKanColimitHomPoint F =
      (Functor.Monoidal.εIso SSet.opFunctor).hom ≫
        SSet.opFunctor.map (MonoidalClosed.id (kanReflectedBousfieldKanColimitObject F).obj) ≫
          kanReflectedBousfieldKanColimitHomComparison F
            (kanReflectedBousfieldKanColimitObject F) := by
  dsimp only [kanReflectedBousfieldKanColimitHomPoint,
    reflectedWeightedColimitHomPointOfMap, kanReflectedBousfieldKanColimitHomComparison,
    kanReflectedBousfieldKanColimitUnderlyingHomIso, Iso.trans_hom]
  rw [← Functor.map_comp_assoc, internalHom_id_pre]
  rfl

/-- 反転した内部 Hom の単位の零単体は通常の恒等射の反転表示。 -/
lemma reflectedKanIdentity_vertex (K : KanObject.{u}) :
    ((Functor.Monoidal.εIso SSet.opFunctor).hom ≫
      SSet.opFunctor.map (MonoidalClosed.id K.obj)).app (Opposite.op ⦋0⦌) PUnit.unit =
        SSet.opObjEquiv.symm (SimplicialCategory.homEquiv' K K (𝟙 K)) := by
  simp only [SimplicialCategory.homEquiv', Equiv.trans_apply, eHomEquiv_id]
  rfl

/-- 構成済みの coherent な余錐の普遍点は、豊穣復元公式の普遍切断点の像に一致する。 -/
lemma bousfieldKanCoherentConePoint_of_end_point
    (F : I ⥤ KanObject.{u}) :
    bousfieldKanCoherentConePoint F =
      (reflectedHomHolimConeComparison F.op
        (Opposite.op (kanReflectedBousfieldKanColimitObject F))).app (Opposite.op ⦋0⦌)
          (ULift.up ((kanReflectedBousfieldKanColimitHomPoint F).app (Opposite.op ⦋0⦌)
            PUnit.unit)) := by
  rw [kanReflectedBousfieldKanColimitHomPoint_eq]
  change (reflectedHomHolimConeComparison F.op
      (Opposite.op (kanReflectedBousfieldKanColimitObject F))).app (Opposite.op ⦋0⦌)
      (ULift.up ((kanReflectedBousfieldKanColimitHomComparison F
        (kanReflectedBousfieldKanColimitObject F)).app (Opposite.op ⦋0⦌)
          (SSet.opObjEquiv.symm (SimplicialCategory.homEquiv' _ _ (𝟙 _))))) =
    (reflectedHomHolimConeComparison F.op
      (Opposite.op (kanReflectedBousfieldKanColimitObject F))).app (Opposite.op ⦋0⦌)
      (ULift.up ((kanReflectedBousfieldKanColimitHomComparison F
        (kanReflectedBousfieldKanColimitObject F)).app (Opposite.op ⦋0⦌)
          (((Functor.Monoidal.εIso SSet.opFunctor).hom ≫
            SSet.opFunctor.map
              (MonoidalClosed.id (kanReflectedBousfieldKanColimitObject F).obj)).app
                (Opposite.op ⦋0⦌) PUnit.unit)))
  rw [reflectedKanIdentity_vertex]

end
end SerrePositivity.InfinityCategories.HomotopyLimits
